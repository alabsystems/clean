// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The importer's `is_large_elim` fixup, decided IN PLACE
//! (`Environment::recompute_imported_large_elim`) once a module's families are
//! resident, answers exactly as the per-part staging copy it replaced did.
//!
//! Two lanes removed that copy on 2026-09-28/29: upstream's `derive_large_elim`
//! decided the environment-free shapes without it and staged the rest per
//! batch; the Phase 1 import lane decided every family on the real environment
//! after passes 1-2, with no copy at all. The integration kept the in-place
//! decision and retargeted upstream's oracle arm here: the copy is kept as the
//! oracle, and the in-place answers must equal it on the same mixed batch.
use clean_kernel::env::{Environment, TrustedEnvExt};
use clean_kernel::expr::{Expr, LevelVec};
use clean_kernel::inductive::{allows_large_elim, Constructor, ConstructorVal, InductiveVal};
use clean_kernel::name::Name;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

/// A single-type, parameterless family whose constructors are `fields -> name`.
fn family(name: &str, sort: Expr, ctors: &[&[Expr]]) -> (InductiveVal, Vec<ConstructorVal>) {
    let ctor_names: Vec<Name> = (0..ctors.len())
        .map(|i| Name::append(&n(name), &format!("c{i}")))
        .collect();
    let ind = InductiveVal {
        name: n(name),
        level_params: vec![],
        type_: sort,
        num_params: 0,
        num_indices: 0,
        all_names: vec![n(name)],
        constructor_names: ctor_names.clone(),
        is_recursive: false,
        is_reflexive: false,
        // The converter's placeholder (`convert.rs`): the fixup must overwrite it.
        is_large_elim: true,
        is_nested: false,
    };
    let vals = ctors
        .iter()
        .zip(ctor_names)
        .enumerate()
        .map(|(idx, (fields, ctor_name))| {
            let mut ty = Expr::const_(n(name), LevelVec::new());
            for field in fields.iter().rev() {
                ty = Expr::arrow(field.clone(), ty);
            }
            ConstructorVal {
                name: ctor_name,
                inductive_name: n(name),
                level_params: vec![],
                type_: ty,
                num_params: 0,
                num_fields: u32::try_from(fields.len()).expect("few fields"),
                constructor_idx: u32::try_from(idx).expect("few constructors"),
            }
        })
        .collect();
    (ind, vals)
}

fn konst(name: &str) -> Expr {
    Expr::const_(n(name), LevelVec::new())
}

fn batch(
    families: Vec<(InductiveVal, Vec<ConstructorVal>)>,
) -> (Vec<InductiveVal>, Vec<ConstructorVal>) {
    let mut inds = Vec::new();
    let mut ctors = Vec::new();
    for (ind, cs) in families {
        inds.push(ind);
        ctors.extend(cs);
    }
    (inds, ctors)
}

fn own_constructors(ind: &InductiveVal, ctors: &[ConstructorVal]) -> Vec<Constructor> {
    ctors
        .iter()
        .filter(|c| c.inductive_name == ind.name)
        .map(|c| Constructor {
            name: c.name.clone(),
            type_: c.type_.clone(),
        })
        .collect()
}

/// The fixup as it stood until 2026-09-28: a copy of `env` per part, with
/// every family of the part staged, and `allows_large_elim` asked for each.
/// Kept as the oracle the in-place decision must agree with.
fn per_part_copy(env: &Environment, inds: &[InductiveVal], ctors: &[ConstructorVal]) -> Vec<bool> {
    let mut staging = env.clone();
    let _ = staging.extend_inductives_structural(inds.iter().cloned());
    let _ = staging.extend_constructors_structural(ctors.iter().cloned());
    inds.iter()
        .map(|ind| {
            allows_large_elim(
                &staging,
                &ind.type_,
                &own_constructors(ind, ctors),
                ind.num_params,
                ind.all_names.len(),
            )
        })
        .collect()
}

/// Register the batch the way the importer's passes 1-2 do, then decide in
/// place; the resident flags are the answer.
fn in_place(env: &mut Environment, inds: &[InductiveVal], ctors: &[ConstructorVal]) -> Vec<bool> {
    assert!(env
        .extend_inductives_structural(inds.iter().cloned())
        .is_empty());
    assert!(env
        .extend_constructors_structural(ctors.iter().cloned())
        .is_empty());
    env.recompute_imported_large_elim(
        inds.iter()
            .map(|ind| (ind.name.clone(), own_constructors(ind, ctors))),
    );
    inds.iter()
        .map(|ind| {
            env.get_inductive(&ind.name)
                .expect("the family is resident")
                .is_large_elim
        })
        .collect()
}

#[test]
fn test_recompute_imported_large_elim_answers_as_the_per_part_copy_did() {
    let (inds, ctors) = batch(vec![
        family("T", Expr::type_(), &[&[]]),
        family("O", Expr::prop(), &[&[], &[]]),
        // `P : Prop` with one field-free constructor: environment-reading shape.
        family("P", Expr::prop(), &[&[]]),
        // `W.c0 : Type -> W`: a non-Prop field not among the indices -> Prop-only.
        family("W", Expr::prop(), &[&[Expr::type_()]]),
        // `R.c0 : R -> R`: a recursive Prop singleton. Large only when `R` is
        // resident while its field is checked -- why the decision needs the
        // family registered, which in place it is.
        family("R", Expr::prop(), &[&[konst("R")]]),
    ]);
    let oracle = per_part_copy(&Environment::new(), &inds, &ctors);
    assert_eq!(
        oracle,
        vec![true, false, true, false, true],
        "T, O, P, W, R"
    );
    let mut env = Environment::new();
    assert_eq!(
        in_place(&mut env, &inds, &ctors),
        oracle,
        "the in-place decision must answer as the per-part copy did"
    );
}

#[test]
fn test_recompute_imported_large_elim_reads_only_what_is_resident() {
    // `Q.c0 : P -> Q` needs `P` to type its field. With `P` unknown the field
    // cannot be checked and `Q` is Prop-only ...
    let (q, q_ctors) = batch(vec![family("Q", Expr::prop(), &[&[konst("P")]])]);
    assert_eq!(in_place(&mut Environment::new(), &q, &q_ctors), vec![false]);
    // ... and with an earlier module's `P : Prop` resident, `Q`'s one field is
    // a Prop and `Q` is large, as the per-part copy of that environment says.
    let mut env = Environment::new();
    let (p, p_ctors) = batch(vec![family("P", Expr::prop(), &[&[]])]);
    in_place(&mut env, &p, &p_ctors);
    let oracle = per_part_copy(&env, &q, &q_ctors);
    assert_eq!(oracle, vec![true]);
    assert_eq!(in_place(&mut env, &q, &q_ctors), oracle);
}

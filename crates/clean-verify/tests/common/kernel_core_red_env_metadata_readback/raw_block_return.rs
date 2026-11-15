// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Finite final-source reconstruction, independent of producer adapters.
//! The declarations are obtained read-only from final kernel records, not the
//! original strict-time/nested auxiliary block. These tests do not establish
//! admission or Rust execution refinement.

use super::{app, build_spec_with_stack, list, run_with_stack, Expr, Level, Name, Readback};
use clean_kernel::inductive::InductiveDecl;
use clean_kernel::Environment;

struct RawBlock {
    source: InductiveDecl,
    levels: Expr,
    params: Expr,
    members: Expr,
    member_terms: Vec<Expr>,
    ctor_terms: Vec<Vec<Expr>>,
    names: Expr,
}

fn captured() -> Expr {
    app("red_ind_ctor", [Expr::const_str("kernel_core_red_env")])
}

fn some(type_: &str, value: Expr) -> Expr {
    app("OptionType.some", [Expr::const_str(type_), value])
}

fn option(type_: &str) -> Expr {
    app("OptionType", [Expr::const_str(type_)])
}

// The actual foundational Eq is universe-polymorphic. The model's Bool,
// raw-record carriers and their OptionType instances all inhabit Type.
fn equality(type_: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [type_, left, right],
    )
}

fn reflexivity(type_: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [type_, value],
    )
}

fn check_proof(readback: &Readback<'_>, proof: Expr, expected: Expr) {
    let actual = readback
        .tc
        .infer_type_full(&proof)
        .expect("actual source-derived theorem application kernel-checks");
    assert!(
        readback.tc.is_def_eq(&actual, &expected),
        "source-derived proof has the required statement\nactual: {actual:?}\nexpected: {expected:?}"
    );
}

fn reconstruct(readback: &Readback<'_>, env: &Environment, root: &str) -> RawBlock {
    let root = env
        .get_inductive(&Name::from_string(root))
        .expect("actual reflected root");
    let source = env
        .inductive_decl_of(&root.name)
        .expect("read-only final stored declaration reconstruction");
    assert_eq!(source.num_params, root.num_params);
    assert_eq!(source.level_params, root.level_params);
    let ordered_names: Vec<_> = source
        .types
        .iter()
        .map(|member| member.name.clone())
        .collect();
    assert_eq!(
        ordered_names, root.all_names,
        "complete ordered final block"
    );
    assert!(
        !source.types.is_empty(),
        "actual Eq/Prod block is inhabited"
    );

    let mut member_terms = Vec::new();
    let mut ctor_terms = Vec::new();
    for member in &source.types {
        let stored = env
            .get_inductive(&member.name)
            .expect("actual block member");
        let signature = env
            .get_const(&member.name)
            .expect("actual member signature");
        assert_eq!(member.name, stored.name);
        assert_eq!(member.type_, stored.type_);
        assert_eq!(signature.name, member.name);
        assert_eq!(signature.type_, member.type_);
        assert_eq!(signature.level_params, source.level_params);
        assert_eq!(stored.level_params, source.level_params);
        assert_eq!(stored.num_params, source.num_params);
        assert_eq!(stored.all_names, ordered_names);
        let names: Vec<_> = member
            .constructors
            .iter()
            .map(|ctor| ctor.name.clone())
            .collect();
        assert_eq!(
            names, stored.constructor_names,
            "complete ordered constructor list"
        );
        let mut constructors = Vec::new();
        for (index, constructor) in member.constructors.iter().enumerate() {
            let actual = env
                .get_constructor(&constructor.name)
                .expect("actual source constructor");
            let signature = env
                .get_const(&constructor.name)
                .expect("actual constructor signature");
            assert_eq!(actual.name, constructor.name);
            assert_eq!(actual.type_, constructor.type_);
            assert_eq!(actual.inductive_name, member.name);
            assert_eq!(
                usize::try_from(actual.constructor_idx).expect("source index fits"),
                index
            );
            assert_eq!(actual.num_params, source.num_params);
            assert_eq!(actual.level_params, source.level_params);
            assert_eq!(signature.name, constructor.name);
            assert_eq!(signature.type_, constructor.type_);
            assert_eq!(signature.level_params, source.level_params);
            constructors.push(app(
                "NamedCtorSource.mk",
                [
                    readback.name(&constructor.name),
                    readback.expr(&constructor.type_),
                ],
            ));
        }
        member_terms.push(app(
            "NamedMemberSource.mk",
            [
                readback.name(&member.name),
                readback.expr(&member.type_),
                list("NamedCtorSource", constructors.clone()),
            ],
        ));
        ctor_terms.push(constructors);
    }
    let levels = list(
        "Name",
        source
            .level_params
            .iter()
            .map(|name| readback.name(name))
            .collect(),
    );
    let params = Expr::nat_lit(u64::from(source.num_params));
    let members = list("NamedMemberSource", member_terms.clone());
    let names = list(
        "Name",
        ordered_names
            .iter()
            .map(|name| readback.name(name))
            .collect(),
    );
    for (value, type_) in [
        (&levels, app("ListType", [Expr::const_str("Name")])),
        (
            &members,
            app("ListType", [Expr::const_str("NamedMemberSource")]),
        ),
    ] {
        let inferred = readback
            .tc
            .infer_type_full(value)
            .expect("independently encoded input is typed");
        assert!(readback.tc.is_def_eq(&inferred, &type_));
    }
    RawBlock {
        source,
        levels,
        params,
        members,
        member_terms,
        ctor_terms,
        names,
    }
}

fn install(raw: &RawBlock, base: Expr) -> Expr {
    app(
        "nsi_raw_install",
        [
            raw.levels.clone(),
            raw.params.clone(),
            raw.members.clone(),
            base,
        ],
    )
}

fn expected_ind(readback: &Readback<'_>, env: &Environment, name: &Name) -> Expr {
    let source = env.get_inductive(name).expect("actual source inductive");
    app(
        "KIndMeta.mk",
        [
            readback.signature(env.get_const(name).expect("actual source signature")),
            Expr::nat_lit(u64::from(source.num_params)),
            Expr::nat_lit(u64::from(source.num_indices)),
            list(
                "Name",
                source
                    .constructor_names
                    .iter()
                    .map(|name| readback.name(name))
                    .collect(),
            ),
            list(
                "Name",
                source
                    .all_names
                    .iter()
                    .map(|name| readback.name(name))
                    .collect(),
            ),
        ],
    )
}

fn expected_ctor(readback: &Readback<'_>, env: &Environment, name: &Name) -> Expr {
    let source = env
        .get_constructor(name)
        .expect("actual source constructor");
    app(
        "KCtorMeta.mk",
        [
            readback.signature(env.get_const(name).expect("actual source signature")),
            readback.name(&source.inductive_name),
            Expr::nat_lit(u64::from(source.num_params)),
            Expr::nat_lit(u64::from(source.num_fields)),
            Expr::nat_lit(u64::from(source.constructor_idx)),
        ],
    )
}

fn compare_source_and_capture(
    readback: &Readback<'_>,
    env: &Environment,
    raw: &RawBlock,
    base: Expr,
) {
    let table = install(raw, base);
    for member in &raw.source.types {
        let actual = readback.some_payload(
            app("kind_for", [table.clone(), readback.name(&member.name)]),
            "KIndMeta",
        );
        readback.equal(
            "raw installed family/source",
            actual.clone(),
            expected_ind(readback, env, &member.name),
            "KIndMeta",
        );
        readback.equal(
            "raw installed family/capture",
            actual.clone(),
            readback.metadata("ind", &member.name),
            "KIndMeta",
        );
        let source = env.get_inductive(&member.name).expect("source family");
        assert!(readback.inductive_counts_match(&actual, source));
        assert!(readback.inductive_block_names_match(&actual, source));
        readback.entry_signature(
            env,
            "ind",
            env.get_const(&member.name).expect("source signature"),
            actual.clone(),
        );
        assert!(readback.typed_equal(
            &app("kind_ctor_names", [actual]),
            &list(
                "Name",
                source
                    .constructor_names
                    .iter()
                    .map(|name| readback.name(name))
                    .collect()
            ),
            &app("ListType", [Expr::const_str("Name")]),
        ));
        assert!(readback.typed_equal(
            &app("kctor_for", [table.clone(), readback.name(&member.name)]),
            &app("OptionType.none", [Expr::const_str("KCtorMeta")]),
            &option("KCtorMeta"),
        ));
        for constructor in &member.constructors {
            let actual = readback.some_payload(
                app(
                    "kctor_for",
                    [table.clone(), readback.name(&constructor.name)],
                ),
                "KCtorMeta",
            );
            readback.equal(
                "raw installed constructor/source",
                actual.clone(),
                expected_ctor(readback, env, &constructor.name),
                "KCtorMeta",
            );
            readback.equal(
                "raw installed constructor/capture",
                actual.clone(),
                readback.metadata("ctor", &constructor.name),
                "KCtorMeta",
            );
            let source = env
                .get_constructor(&constructor.name)
                .expect("source constructor");
            for (projector, value) in [
                ("kctor_num_params", source.num_params),
                ("kctor_num_fields", source.num_fields),
                ("kctor_index", source.constructor_idx),
            ] {
                readback.equal(
                    projector,
                    app(projector, [actual.clone()]),
                    Expr::nat_lit(u64::from(value)),
                    "Nat",
                );
            }
            readback.equal(
                "raw constructor parent",
                app("kctor_parent", [actual.clone()]),
                readback.name(&source.inductive_name),
                "Name",
            );
            readback.entry_signature(
                env,
                "ctor",
                env.get_const(&constructor.name).expect("source signature"),
                actual,
            );
            assert!(readback.typed_equal(
                &app(
                    "kind_for",
                    [table.clone(), readback.name(&constructor.name)]
                ),
                &app("OptionType.none", [Expr::const_str("KIndMeta")]),
                &option("KIndMeta"),
            ));
        }
    }
}

fn check_source(root: &'static str, params: u32, indices: u32, fields: u32) {
    run_with_stack(move || {
        let spec = build_spec_with_stack();
        let env = spec.env();
        let readback = Readback::new(env);
        let raw = reconstruct(&readback, env, root);
        assert_eq!(raw.source.types.len(), 1);
        let member = &raw.source.types[0];
        let stored = env.get_inductive(&member.name).expect("actual root");
        assert_eq!((stored.num_params, stored.num_indices), (params, indices));
        assert_eq!(member.constructors.len(), 1);
        let constructor = env
            .get_constructor(&member.constructors[0].name)
            .expect("actual constructor");
        assert_eq!(
            (constructor.num_params, constructor.num_fields),
            (params, fields)
        );
        for base in [Expr::const_str("IndCtorEnv.empty"), captured()] {
            compare_source_and_capture(&readback, env, &raw, base);
        }
    });
}

#[test]
fn test_raw_installer_final_eq_source_matches_capture() {
    // Observations are asserted after actual final-record reconstruction.
    check_source("Eq", 2, 1, 0);
}

#[test]
fn test_raw_installer_final_prod_source_matches_capture() {
    check_source("ProdType", 2, 0, 2);
}

#[test]
fn test_raw_installer_eq_keeps_unrelated_captured_prod_lookups() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let env = spec.env();
        let readback = Readback::new(env);
        let raw = reconstruct(&readback, env, "Eq");
        let prod = env
            .get_inductive(&Name::from_string("ProdType"))
            .expect("actual unrelated family");
        assert!(raw
            .source
            .types
            .iter()
            .all(|member| member.name != prod.name));
        let table = install(&raw, captured());
        for (lookup, name, payload) in std::iter::once(("kind_for", &prod.name, "KIndMeta")).chain(
            prod.constructor_names
                .iter()
                .map(|name| ("kctor_for", name, "KCtorMeta")),
        ) {
            assert!(readback.typed_equal(
                &app(lookup, [table.clone(), readback.name(name)]),
                &app(lookup, [captured(), readback.name(name)]),
                &option(payload),
            ));
        }
    });
}

#[test]
fn test_raw_installer_actual_inputs_feed_whole_and_selected_theorems() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let env = spec.env();
        let readback = Readback::new(env);
        for root in ["Eq", "ProdType"] {
            let raw = reconstruct(&readback, env, root);
            let check = app(
                "nwr_raw_return_b",
                [raw.levels.clone(), raw.params.clone(), raw.members.clone()],
            );
            readback.equal(
                "actual final raw whole computation",
                check.clone(),
                Expr::const_str("Bool.true"),
                "Bool",
            );
            let run = reflexivity(Expr::const_str("Bool"), Expr::const_str("Bool.true"));
            check_proof(
                &readback,
                run.clone(),
                equality(Expr::const_str("Bool"), check, Expr::const_str("Bool.true")),
            );
            for base in [Expr::const_str("IndCtorEnv.empty"), captured()] {
                let proof = app(
                    "nwr_installed_return_of_raw",
                    [
                        raw.levels.clone(),
                        raw.params.clone(),
                        raw.members.clone(),
                        base.clone(),
                        run.clone(),
                    ],
                );
                let installed_check = app(
                    "nrb_block_return_b",
                    [install(&raw, base.clone()), raw.names.clone()],
                );
                check_proof(
                    &readback,
                    proof,
                    equality(
                        Expr::const_str("Bool"),
                        installed_check,
                        Expr::const_str("Bool.true"),
                    ),
                );
                for (mi, member) in raw.source.types.iter().enumerate() {
                    for (ci, constructor) in member.constructors.iter().enumerate() {
                        let member_at = reflexivity(
                            option("NamedMemberSource"),
                            some("NamedMemberSource", raw.member_terms[mi].clone()),
                        );
                        let ctor_at = reflexivity(
                            option("NamedCtorSource"),
                            some("NamedCtorSource", raw.ctor_terms[mi][ci].clone()),
                        );
                        let proof = app(
                            "nwr_selected_strict_facts",
                            [
                                raw.levels.clone(),
                                raw.params.clone(),
                                raw.members.clone(),
                                base.clone(),
                                Expr::nat_lit(u64::try_from(mi).expect("finite source position")),
                                raw.member_terms[mi].clone(),
                                Expr::nat_lit(
                                    u64::try_from(ci).expect("finite constructor position"),
                                ),
                                raw.ctor_terms[mi][ci].clone(),
                                run.clone(),
                                member_at,
                                ctor_at,
                            ],
                        );
                        let former = env
                            .get_inductive(&member.name)
                            .expect("actual selected former");
                        let expected = app(
                            "NamedStrictAppFacts",
                            [
                                raw.names.clone(),
                                app("nig_param_levels", [raw.levels.clone()]),
                                readback.name(&member.name),
                                app("count_pi", [readback.expr(&constructor.type_)]),
                                raw.params.clone(),
                                Expr::nat_lit(u64::from(former.num_indices)),
                                app("return_type", [readback.expr(&constructor.type_)]),
                            ],
                        );
                        check_proof(&readback, proof, expected);
                    }
                }
            }
        }
    });
}

#[test]
fn test_raw_installer_final_source_corruptions_are_detected() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let env = spec.env();
        let readback = Readback::new(env);
        let raw = reconstruct(&readback, env, "Eq");
        assert_eq!(raw.source.types.len(), 1);
        let member = &raw.source.types[0];
        assert_eq!(member.constructors.len(), 1);
        let constructor = &member.constructors[0];
        let empty = Expr::const_str("IndCtorEnv.empty");
        let good_table = install(&raw, empty.clone());
        let expected = some("KIndMeta", expected_ind(&readback, env, &member.name));
        assert!(readback.typed_equal(
            &app(
                "kind_for",
                [good_table.clone(), readback.name(&member.name)]
            ),
            &expected,
            &option("KIndMeta")
        ));

        // Deleting a source-listed constructor is observable against the
        // unchanged source/capture, even though an empty ctor fold is allowed.
        let no_ctors_member = app(
            "NamedMemberSource.mk",
            [
                readback.name(&member.name),
                readback.expr(&member.type_),
                list("NamedCtorSource", Vec::new()),
            ],
        );
        let no_ctors = list("NamedMemberSource", vec![no_ctors_member]);
        let missing_table = app(
            "nsi_raw_install",
            [
                raw.levels.clone(),
                raw.params.clone(),
                no_ctors.clone(),
                empty.clone(),
            ],
        );
        assert!(!readback.typed_equal(
            &app(
                "kind_for",
                [missing_table.clone(), readback.name(&member.name)]
            ),
            &expected,
            &option("KIndMeta")
        ));
        assert!(readback.typed_equal(
            &app(
                "kctor_for",
                [missing_table, readback.name(&constructor.name)]
            ),
            &app("OptionType.none", [Expr::const_str("KCtorMeta")]),
            &option("KCtorMeta"),
        ));
        readback.equal(
            "empty constructors are not a completeness refusal",
            app(
                "nwr_raw_return_b",
                [raw.levels.clone(), raw.params.clone(), no_ctors],
            ),
            Expr::const_str("Bool.true"),
            "Bool",
        );

        let changed_params = app(
            "nsi_raw_install",
            [
                raw.levels.clone(),
                Expr::nat_lit(u64::from(raw.source.num_params) + 1),
                raw.members.clone(),
                empty.clone(),
            ],
        );
        assert!(!readback.typed_equal(
            &app("kind_for", [changed_params, readback.name(&member.name)]),
            &expected,
            &option("KIndMeta")
        ));

        // This raw type mutation changes the signature. Eq.refl's derived
        // field count stays zero: subtracting two parameters saturates at zero.
        let changed_ctor = app(
            "NamedCtorSource.mk",
            [
                readback.name(&constructor.name),
                app("KExpr.sort", [Expr::const_str("Level.zero")]),
            ],
        );
        let changed_member = app(
            "NamedMemberSource.mk",
            [
                readback.name(&member.name),
                readback.expr(&member.type_),
                list("NamedCtorSource", vec![changed_ctor]),
            ],
        );
        let changed_members = list("NamedMemberSource", vec![changed_member]);
        let changed_table = app(
            "nsi_raw_install",
            [
                raw.levels.clone(),
                raw.params.clone(),
                changed_members.clone(),
                empty,
            ],
        );
        let expected_ctor = some(
            "KCtorMeta",
            expected_ctor(&readback, env, &constructor.name),
        );
        assert!(readback.typed_equal(
            &app("kctor_for", [good_table, readback.name(&constructor.name)]),
            &expected_ctor,
            &option("KCtorMeta")
        ));
        assert!(!readback.typed_equal(
            &app(
                "kctor_for",
                [changed_table, readback.name(&constructor.name)]
            ),
            &expected_ctor,
            &option("KCtorMeta")
        ));
        readback.equal(
            "mutated raw return refuses",
            app(
                "nwr_raw_return_b",
                [raw.levels, raw.params, changed_members],
            ),
            Expr::const_str("Bool.false"),
            "Bool",
        );
    });
}

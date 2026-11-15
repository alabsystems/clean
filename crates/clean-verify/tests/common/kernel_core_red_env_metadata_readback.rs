// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Read the emitted metadata back through the actual kernel, independently of
//! the producer's expression adapter and renderer. This is finite source/data
//! agreement, not a proof of Rust execution or general inductive admission.
//! Stored `all_names` is checked as ordered source data; it is not asserted to
//! be the pre-restoration strict-admission context for nested families.
//!
//! Included by the existing fidelity integration target; it shares that
//! process's FULL_SPEC cache and is not a separate Cargo test target.

use super::{
    build_spec_with_stack, parse_interning_tsv, run_with_stack, ConstantKind, Expr, ExprKind, Name,
    TypeChecker, COMMITTED_DEF_SCRIPT, COMMITTED_INTERNING_TSV, REFLECT_INDUCTIVES,
};
use clean_kernel::{ConstantInfo, Environment, InductiveVal, Level};
use std::collections::BTreeMap;

#[path = "kernel_core_red_env_metadata_readback/raw_block_return.rs"]
mod raw_block_return;

fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_str(name), args)
}

fn list(element_type: &str, values: Vec<Expr>) -> Expr {
    values.into_iter().rev().fold(
        app("ListType.nil", [Expr::const_str(element_type)]),
        |tail, value| {
            app(
                "ListType.cons",
                [Expr::const_str(element_type), value, tail],
            )
        },
    )
}

/// The independent expectations are constructed from actual source records,
/// not Reflected* records, SpecExpr, reflect_definition_expr or kexpr_term.
/// The validated TSV remains the explicitly documented name-encoding boundary.
struct Readback<'a> {
    tc: TypeChecker<'a>,
    tags: BTreeMap<String, u64>,
}

impl<'a> Readback<'a> {
    fn new(env: &'a Environment) -> Self {
        Self {
            tc: TypeChecker::new(env),
            tags: parse_interning_tsv(COMMITTED_INTERNING_TSV)
                .expect("validate the complete committed name table"),
        }
    }

    fn tag(&self, source: &Name) -> u64 {
        *self
            .tags
            .get(&source.to_string())
            .unwrap_or_else(|| panic!("actual source name {source} is not interned"))
    }

    fn name(&self, source: &Name) -> Expr {
        app(
            "Name.str",
            [
                Expr::const_str("Name.anonymous"),
                Expr::nat_lit(self.tag(source)),
            ],
        )
    }

    fn level(&self, source: &Level) -> Expr {
        match source {
            Level::Zero => Expr::const_str("Level.zero"),
            Level::Succ(a) => app("Level.succ", [self.level(a)]),
            Level::Max(a, b) => app("Level.max", [self.level(a), self.level(b)]),
            Level::IMax(a, b) => app("Level.imax", [self.level(a), self.level(b)]),
            Level::Param(name) => app("Level.param", [self.name(name)]),
        }
    }

    fn expr(&self, source: &Expr) -> Expr {
        match source.kind() {
            ExprKind::MData(_, inner) => self.expr(inner),
            ExprKind::BVar(index) => app("KExpr.bvar", [Expr::nat_lit(u64::from(*index))]),
            ExprKind::Sort(level) => app("KExpr.sort", [self.level(level)]),
            ExprKind::Const(name, levels) => app(
                "KExpr.const",
                [
                    self.name(name),
                    list(
                        "Level",
                        levels.iter().map(|level| self.level(level)).collect(),
                    ),
                ],
            ),
            ExprKind::App(a, b) => app("KExpr.app", [self.expr(a), self.expr(b)]),
            ExprKind::Lam(_, a, b) => app("KExpr.lam", [self.expr(a), self.expr(b)]),
            ExprKind::Pi(_, a, b) => app("KExpr.pi", [self.expr(a), self.expr(b)]),
            ExprKind::Let(_, ty, value, body, _) => app(
                "KExpr.let_",
                [self.expr(ty), self.expr(value), self.expr(body)],
            ),
            other => {
                panic!("actual source node has no image in this bounded metadata slice: {other:?}")
            }
        }
    }

    fn signature(&self, source: &ConstantInfo) -> Expr {
        assert_eq!(source.kind, ConstantKind::Definition);
        assert!(
            source.value.is_none(),
            "source metadata has signature-only entries"
        );
        app(
            "KConstSig.mk",
            [
                list(
                    "Name",
                    source
                        .level_params
                        .iter()
                        .map(|name| self.name(name))
                        .collect(),
                ),
                self.expr(&source.type_),
            ],
        )
    }

    fn typed_equal(&self, actual: &Expr, expected: &Expr, type_: &Expr) -> bool {
        for term in [actual, expected] {
            let inferred = self.tc.infer_type_full(term).unwrap_or_else(|error| {
                panic!("readback expression must kernel-check: {error:?}\n{term:?}")
            });
            assert!(
                self.tc.is_def_eq(&inferred, type_),
                "readback has wrong type: {inferred:?}"
            );
        }
        self.tc.is_def_eq(actual, expected)
    }

    fn equal(&self, label: &str, actual: Expr, expected: Expr, type_: &str) {
        assert!(
            self.typed_equal(&actual, &expected, &Expr::const_str(type_)),
            "emitted metadata/source disagreement at {label}\nactual: {actual:?}\nexpected: {expected:?}"
        );
    }

    fn some_payload(&self, lookup: Expr, payload_type: &str) -> Expr {
        let inferred = self
            .tc
            .infer_type_full(&lookup)
            .expect("generated lookup kernel-checks");
        assert!(self.tc.is_def_eq(
            &inferred,
            &app("OptionType", [Expr::const_str(payload_type)])
        ));
        let reduced = self.tc.whnf(&lookup);
        assert!(
            matches!(reduced.get_app_fn().kind(), ExprKind::Const(name, _) if *name == Name::from_string("OptionType.some")),
            "generated lookup must actually reduce to some, not be absent/stuck: {reduced:?}"
        );
        let args = reduced.get_app_args();
        assert_eq!(args.len(), 2, "OptionType.some type and payload");
        Expr::clone(args[1])
    }

    fn metadata(&self, kind: &str, source_name: &Name) -> Expr {
        let (lookup, payload) = match kind {
            "ind" => ("kind_for", "KIndMeta"),
            "ctor" => ("kctor_for", "KCtorMeta"),
            _ => panic!("not a metadata kind: {kind}"),
        };
        self.some_payload(
            app(
                lookup,
                [
                    app("red_ind_ctor", [Expr::const_str("kernel_core_red_env")]),
                    self.name(source_name),
                ],
            ),
            payload,
        )
    }

    fn signature_fields(&self, label: &str, actual: Expr, source: &ConstantInfo) {
        let expected = self.signature(source);
        self.equal(label, actual.clone(), expected, "KConstSig");
        let parameters = app("kconst_params", [actual.clone()]);
        let expected_parameters = list(
            "Name",
            source
                .level_params
                .iter()
                .map(|name| self.name(name))
                .collect(),
        );
        assert!(
            self.typed_equal(
                &parameters,
                &expected_parameters,
                &app("ListType", [Expr::const_str("Name")])
            ),
            "{label}: ordered universe parameters"
        );
        self.equal(
            label,
            app("kconst_type", [actual]),
            self.expr(&source.type_),
            "KExpr",
        );
    }

    fn data_atom(&self, env: &Environment, atom: &str, type_: &str) {
        let source = env
            .get_const(&Name::from_string(atom))
            .unwrap_or_else(|| panic!("missing emitted data {atom}"));
        assert_eq!(
            source.kind,
            ConstantKind::Definition,
            "{atom} must not be opaque data"
        );
        let value = source.value.as_ref().expect("emitted data has a body");
        self.equal(atom, Expr::const_str(atom), value.clone(), type_);
    }

    fn entry_signature(&self, env: &Environment, kind: &str, source: &ConstantInfo, meta: Expr) {
        let tag = self.tag(&source.name);
        let atom = format!("kcre_{kind}_signature_{tag}");
        self.data_atom(env, &atom, "KConstSig");
        self.signature_fields(&atom, Expr::const_str(&atom), source);
        self.signature_fields(
            &format!("{} metadata", source.name),
            app(
                if kind == "ind" {
                    "kind_sig"
                } else {
                    "kctor_sig"
                },
                [meta],
            ),
            source,
        );
        let stored = self.some_payload(
            app("kcre_ind_ctor_tenv", [self.name(&source.name)]),
            "KConstSig",
        );
        self.signature_fields(&format!("{} shared KDeclEnv", source.name), stored, source);
    }

    fn inductive_counts_match(&self, meta: &Expr, source: &InductiveVal) -> bool {
        let params = self.typed_equal(
            &app("kind_num_params", [meta.clone()]),
            &Expr::nat_lit(u64::from(source.num_params)),
            &Expr::const_str("Nat"),
        );
        let indices = self.typed_equal(
            &app("kind_num_indices", [meta.clone()]),
            &Expr::nat_lit(u64::from(source.num_indices)),
            &Expr::const_str("Nat"),
        );
        params && indices
    }

    fn inductive_block_names_match(&self, meta: &Expr, source: &InductiveVal) -> bool {
        self.typed_equal(
            &app("kind_all_names", [meta.clone()]),
            &list(
                "Name",
                source
                    .all_names
                    .iter()
                    .map(|name| self.name(name))
                    .collect(),
            ),
            &app("ListType", [Expr::const_str("Name")]),
        )
    }
}

#[test]
fn test_emitted_projection_metadata_readback_matches_every_source_record() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let env = spec.env();
        let readback = Readback::new(env);
        for (atom, ty) in [
            ("kcre_ind_ctor_env", "IndCtorEnv"),
            ("kcre_ind_ctor_tenv", "KDeclEnv"),
            ("kernel_core_red_env", "RedEnv"),
        ] {
            readback.data_atom(env, atom, ty);
        }
        let mut constructor_count = 0;
        for name in REFLECT_INDUCTIVES {
            let name = Name::from_string(name);
            let source = env
                .get_inductive(&name)
                .expect("allowlisted source inductive");
            assert_eq!(source.name, name);
            let ci = env
                .get_const(&source.name)
                .expect("same-name source signature");
            assert_eq!(ci.name, source.name);
            assert_eq!(ci.type_, source.type_);
            assert_eq!(ci.level_params, source.level_params);
            let meta = readback.metadata("ind", &source.name);
            let atom = format!("kcre_ind_meta_{}", readback.tag(&source.name));
            readback.data_atom(env, &atom, "KIndMeta");
            readback.equal(&atom, meta.clone(), Expr::const_str(&atom), "KIndMeta");
            assert!(
                readback.inductive_counts_match(&meta, source),
                "{}: parameter/index counts",
                source.name
            );
            let names = app("kind_ctor_names", [meta.clone()]);
            let expected_names = list(
                "Name",
                source
                    .constructor_names
                    .iter()
                    .map(|name| readback.name(name))
                    .collect(),
            );
            assert!(
                readback.typed_equal(
                    &names,
                    &expected_names,
                    &app("ListType", [Expr::const_str("Name")])
                ),
                "{}: ordered constructor identities",
                source.name
            );
            assert!(
                readback.inductive_block_names_match(&meta, source),
                "{}: final stored ordered block names",
                source.name
            );
            readback.entry_signature(env, "ind", ci, meta);
            let wrong_kind = app(
                "kctor_for",
                [
                    Expr::const_str("kcre_ind_ctor_env"),
                    readback.name(&source.name),
                ],
            );
            assert!(readback.typed_equal(
                &wrong_kind,
                &app("OptionType.none", [Expr::const_str("KCtorMeta")]),
                &app("OptionType", [Expr::const_str("KCtorMeta")])
            ));

            for (index, name) in source.constructor_names.iter().enumerate() {
                let ctor = env
                    .get_constructor(name)
                    .expect("actual ordered constructor");
                assert_eq!(&ctor.name, name);
                assert_eq!(ctor.inductive_name, source.name);
                assert_eq!(ctor.constructor_idx as usize, index);
                assert_eq!(ctor.num_params, source.num_params);
                assert_eq!(ctor.level_params, source.level_params);
                let ci = env
                    .get_const(&ctor.name)
                    .expect("same-name constructor signature");
                assert_eq!(ci.name, ctor.name);
                assert_eq!(ci.type_, ctor.type_);
                assert_eq!(ci.level_params, ctor.level_params);
                let meta = readback.metadata("ctor", &ctor.name);
                let atom = format!("kcre_ctor_meta_{}", readback.tag(&ctor.name));
                readback.data_atom(env, &atom, "KCtorMeta");
                readback.equal(&atom, meta.clone(), Expr::const_str(&atom), "KCtorMeta");
                for (projector, value) in [
                    ("kctor_num_params", ctor.num_params),
                    ("kctor_num_fields", ctor.num_fields),
                    ("kctor_index", ctor.constructor_idx),
                ] {
                    readback.equal(
                        &format!("{} {projector}", ctor.name),
                        app(projector, [meta.clone()]),
                        Expr::nat_lit(u64::from(value)),
                        "Nat",
                    );
                }
                readback.equal(
                    &format!("{} parent", ctor.name),
                    app("kctor_parent", [meta.clone()]),
                    readback.name(&ctor.inductive_name),
                    "Name",
                );
                readback.entry_signature(env, "ctor", ci, meta);
                let wrong_kind = app(
                    "kind_for",
                    [
                        Expr::const_str("kcre_ind_ctor_env"),
                        readback.name(&ctor.name),
                    ],
                );
                assert!(readback.typed_equal(
                    &wrong_kind,
                    &app("OptionType.none", [Expr::const_str("KIndMeta")]),
                    &app("OptionType", [Expr::const_str("KIndMeta")])
                ));
                constructor_count += 1;
            }
        }
        assert!(
            constructor_count > REFLECT_INDUCTIVES.len(),
            "nonempty, multi-constructor census"
        );

        // Eq's textual declaration starts with one parameter, but fixed-index
        // promotion has already produced this final stored 2/1 boundary.
        let eq = env
            .get_inductive(&Name::from_string("Eq"))
            .expect("actual admitted Eq metadata");
        assert_eq!((eq.num_params, eq.num_indices), (2, 1));
        assert_eq!(eq.all_names, vec![eq.name.clone()]);
        assert_eq!(eq.constructor_names.len(), 1);
        let refl = env
            .get_constructor(&eq.constructor_names[0])
            .expect("actual ordered Eq constructor");
        assert_eq!((refl.num_params, refl.num_fields), (2, 0));
        assert_eq!(refl.inductive_name, eq.name);
        for (atom, ty, expected) in [
            ("kcre_eq_type_name", "Name", readback.name(&eq.name)),
            ("kcre_eq_refl_name", "Name", readback.name(&refl.name)),
            (
                "kcre_eq_type_signature",
                "KConstSig",
                readback.signature(env.get_const(&eq.name).expect("actual Eq signature")),
            ),
            (
                "kcre_eq_refl_signature",
                "KConstSig",
                readback.signature(env.get_const(&refl.name).expect("actual Eq.refl signature")),
            ),
            (
                "kcre_eq_ind_meta",
                "KIndMeta",
                readback.metadata("ind", &eq.name),
            ),
            (
                "kcre_eq_refl_meta",
                "KCtorMeta",
                readback.metadata("ctor", &refl.name),
            ),
        ] {
            readback.data_atom(env, atom, ty);
            readback.equal(atom, Expr::const_str(atom), expected, ty);
            let description = &spec
                .definitions()
                .get(atom)
                .expect("registered Eq alias")
                .description;
            assert!(
                description.starts_with("Generated actual-source inductive/constructor metadata")
            );
            assert!(!description.contains("Generated interned-name constant"));
        }

        // Independently construct the real source caller, infer its type, and
        // compare the emitted KExpr atoms (not merely ReflectedProjectionWitness).
        let prod = env
            .get_inductive(&Name::from_string("ProdType"))
            .expect("actual ProdType");
        assert_eq!(prod.constructor_names.len(), 1);
        let constant = |name: &str| {
            Expr::const_(
                env.get_const(&Name::from_string(name))
                    .expect("source constant")
                    .name
                    .clone(),
                vec![],
            )
        };
        let nat = constant("Nat");
        let zero = constant("Nat.zero");
        let one = Expr::app(constant("Nat.succ"), zero.clone());
        let value = Expr::apps(
            Expr::const_(prod.constructor_names[0].clone(), vec![]),
            [nat.clone(), nat.clone(), zero, one],
        );
        let inferred = readback
            .tc
            .infer_type_full(&value)
            .expect("actual source caller checks");
        assert_eq!(
            inferred,
            Expr::apps(Expr::const_(prod.name.clone(), vec![]), [nat.clone(), nat])
        );
        for (atom, source) in [
            ("kcre_witness_prod_value", &value),
            ("kcre_witness_prod_type", &inferred),
        ] {
            readback.data_atom(env, atom, "KExpr");
            readback.equal(atom, Expr::const_str(atom), readback.expr(source), "KExpr");
        }
    });
}

#[test]
fn test_emitted_projection_metadata_readback_refuses_rendered_field_swap() {
    run_with_stack(|| {
        let full = build_spec_with_stack();
        let source = full
            .env()
            .get_inductive(&Name::from_string("ProdType"))
            .expect("actual source ProdType");
        let good = Readback::new(full.env());
        assert_ne!(
            source.num_params, source.num_indices,
            "mutation must change two distinct fields"
        );
        assert!(
            good.inductive_counts_match(&good.metadata("ind", &source.name), source),
            "unmutated emitted table is the positive control"
        );
        let tag = good.tag(&source.name);
        let prefix =
            format!("def kcre_ind_meta_{tag} : KIndMeta := KIndMeta.mk kcre_ind_signature_{tag} ");
        let line = COMMITTED_DEF_SCRIPT
            .lines()
            .find(|line| line.starts_with(&prefix))
            .expect("actual emitted metadata line");
        let original = format!(
            "{prefix}kcre_nat_{} kcre_nat_{} ",
            source.num_params, source.num_indices
        );
        assert!(
            line.starts_with(&original),
            "pin the actual rendered field positions"
        );
        assert_eq!(
            COMMITTED_DEF_SCRIPT.matches(&original).count(),
            1,
            "one exact mutation site"
        );
        let swapped = format!(
            "{prefix}kcre_nat_{} kcre_nat_{} ",
            source.num_indices, source.num_params
        );
        let script = COMMITTED_DEF_SCRIPT.replacen(&original, &swapped, 1);
        assert_eq!(
            COMMITTED_DEF_SCRIPT
                .lines()
                .zip(script.lines())
                .filter(|(a, b)| a != b)
                .count(),
            1
        );

        // Replay the real script, with only that rendered data change, using
        // public declaration elaboration in an artifact-independent seed. Do
        // not ask the full proof corpus to fail first at an unrelated theorem.
        let mut mutated =
            clean_verify::Specification::new_red_env_reflection_seed().expect("independent seed");
        for line in script
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty())
        {
            mutated
                .add_recursive_def(line, "Fidelity rendered-field mutation control")
                .unwrap_or_else(|error| {
                    panic!("well-typed mutated data must register: {line}\n{error:?}")
                });
        }
        let bad = Readback::new(mutated.env());
        let meta = bad.metadata("ind", &source.name);
        assert!(
            !bad.inductive_counts_match(&meta, source),
            "the same source readback must detect a renderer field-order bug"
        );
        for (projector, swapped_value) in [
            ("kind_num_params", source.num_indices),
            ("kind_num_indices", source.num_params),
        ] {
            bad.equal(
                "exact mutated field",
                app(projector, [meta.clone()]),
                Expr::nat_lit(u64::from(swapped_value)),
                "Nat",
            );
        }
        let ci = full
            .env()
            .get_const(&source.name)
            .expect("unchanged real source signature");
        bad.entry_signature(mutated.env(), "ind", ci, meta);
    });
}

#[test]
fn test_emitted_projection_metadata_readback_refuses_rendered_block_name() {
    run_with_stack(|| {
        let full = build_spec_with_stack();
        let source = full
            .env()
            .get_inductive(&Name::from_string("ProdType"))
            .expect("actual source ProdType");
        let good = Readback::new(full.env());
        assert_eq!(source.all_names, vec![source.name.clone()]);
        assert_eq!(source.constructor_names.len(), 1);
        let wrong_name = &source.constructor_names[0];
        assert_ne!(wrong_name, &source.name);
        assert!(
            good.inductive_block_names_match(&good.metadata("ind", &source.name), source),
            "unmutated emitted block is the positive control"
        );
        let tag = good.tag(&source.name);
        let prefix =
            format!("def kcre_ind_meta_{tag} : KIndMeta := KIndMeta.mk kcre_ind_signature_{tag} ");
        let line = COMMITTED_DEF_SCRIPT
            .lines()
            .find(|line| line.starts_with(&prefix))
            .expect("actual emitted metadata line");
        let original = format!("(ListType.cons Name kcre_name_{tag} (ListType.nil Name))");
        let retained = line
            .strip_suffix(&original)
            .expect("final stored block occupies the fifth field");
        let replacement = format!(
            "{retained}(ListType.cons Name kcre_name_{} (ListType.nil Name))",
            good.tag(wrong_name)
        );
        assert_eq!(COMMITTED_DEF_SCRIPT.matches(line).count(), 1);
        let script = COMMITTED_DEF_SCRIPT.replacen(line, &replacement, 1);
        assert_eq!(
            COMMITTED_DEF_SCRIPT
                .lines()
                .zip(script.lines())
                .filter(|(a, b)| a != b)
                .count(),
            1
        );
        let mut mutated =
            clean_verify::Specification::new_red_env_reflection_seed().expect("independent seed");
        for line in script
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty())
        {
            mutated
                .add_recursive_def(line, "Fidelity rendered-block mutation control")
                .unwrap_or_else(|error| {
                    panic!("well-typed mutated data must register: {line}\n{error:?}")
                });
        }
        let bad = Readback::new(mutated.env());
        let meta = bad.metadata("ind", &source.name);
        assert!(
            !bad.inductive_block_names_match(&meta, source),
            "independent source readback must detect the wrong stored block"
        );
        assert!(bad.inductive_counts_match(&meta, source));
        assert!(bad.typed_equal(
            &app("kind_all_names", [meta.clone()]),
            &list("Name", vec![good.name(wrong_name)]),
            &app("ListType", [Expr::const_str("Name")])
        ));
        let ci = full
            .env()
            .get_const(&source.name)
            .expect("source signature");
        bad.entry_signature(mutated.env(), "ind", ci, meta);
    });
}

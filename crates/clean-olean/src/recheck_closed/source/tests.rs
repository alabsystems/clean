// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::{BinderInfo, ConstantOrigin, Declaration, Expr, Level};

fn n(s: &str) -> Name {
    Name::from_string(s)
}
fn fixture() -> (Arc<Environment>, Arc<Environment>, BTreeSet<Name>) {
    let base = Environment::with_prelude();
    let mut checked = base.clone();
    checked
        .add_decl(Declaration::Definition {
            name: n("query"),
            level_params: vec![],
            type_: Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Nat")),
            value: Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0)),
            is_reducible: false,
        })
        .unwrap();
    let mut source = base.clone();
    assert!(source
        .extend_constants_structural(std::iter::once(
            checked.get_const(&n("query")).unwrap().clone()
        ))
        .is_empty());
    assert!(source.set_constant_origin(
        n("query"),
        ConstantOrigin::olean_import(Some("Source".into()))
    ));
    (
        Arc::new(base),
        Arc::new(source),
        BTreeSet::from([n("query")]),
    )
}
#[test]
fn replayed_source_retains_original_and_actual_replayed_provenance() {
    let (base, source, roots) = fixture();
    assert!(source.constant_needs_recheck(&n("query")));
    let replay =
        ReplayedImportedSource::check(Arc::clone(&base), Arc::clone(&source), roots.clone())
            .unwrap();
    replay.require_context(&base, &source, &roots).unwrap();
    assert!(replay.verdict().passed(false));
    replay.require_record(&source, &n("query")).unwrap();
    assert!(replay
        .original_environment()
        .constant_needs_recheck(&n("query")));
    assert!(!replay
        .checked_environment()
        .constant_needs_recheck(&n("query")));
    assert_eq!(
        replay.checked_constant(&n("query")).unwrap().value,
        source.get_const(&n("query")).unwrap().value
    );
    assert!(matches!(
        replay.checked_constant(&n("unrequested")),
        Err(ReplayedSourceError::Outside(_))
    ));
}
#[test]
fn replayed_source_rejects_foreign_equal_rows_bases_and_root_sets() {
    let (base, source, roots) = fixture();
    let replay =
        ReplayedImportedSource::check(Arc::clone(&base), Arc::clone(&source), roots.clone())
            .unwrap();
    assert!(matches!(
        replay.require_context(&Arc::new((*base).clone()), &source, &roots),
        Err(ReplayedSourceError::ForeignBase)
    ));
    assert!(matches!(
        replay.require_context(&base, &Arc::new((*source).clone()), &roots),
        Err(ReplayedSourceError::ForeignSource)
    ));
    assert!(matches!(
        replay.require_context(&base, &source, &BTreeSet::from([n("Nat")])),
        Err(ReplayedSourceError::DifferentRoots)
    ));
}
#[test]
fn replayed_source_changed_row_or_runtime_metadata_cannot_reuse_receipt() {
    let (base, mut source, roots) = fixture();
    let replay =
        ReplayedImportedSource::check(Arc::clone(&base), Arc::clone(&source), roots.clone())
            .unwrap();
    Arc::make_mut(&mut source).register_extern(n("query"), "different_runtime".into());
    assert!(matches!(
        replay.require_context(&base, &source, &roots),
        Err(ReplayedSourceError::ForeignSource)
    ));
    assert!(matches!(
        replay.require_record(&source, &n("query")),
        Err(ReplayedSourceError::SourceChanged(_))
    ));
    assert!(replay
        .original_environment()
        .get_extern(&n("query"))
        .is_none());
}
#[test]
fn replayed_source_fresh_check_never_reuses_prior_admitted_name_for_changed_body() {
    let (base, source, roots) = fixture();
    let first =
        ReplayedImportedSource::check(Arc::clone(&base), Arc::clone(&source), roots.clone())
            .unwrap();
    let mut changed = (*source).clone();
    let mut info = changed.get_const(&n("query")).unwrap().clone();
    info.value = Some(Expr::sort(Level::zero()));
    changed.forget_decl(&n("query"));
    assert!(changed
        .extend_constants_structural(std::iter::once(info))
        .is_empty());
    changed.set_constant_origin(
        n("query"),
        ConstantOrigin::olean_import(Some("Changed".into())),
    );
    assert!(matches!(
        ReplayedImportedSource::check(base, Arc::new(changed), roots),
        Err(ReplayedSourceError::Replay(..))
    ));
    assert!(first.checked_constant(&n("query")).is_ok());
}
#[test]
fn replayed_source_unverified_given_base_is_not_kernel_source_authority() {
    let (_base, source, roots) = fixture();
    let base = Arc::clone(&source);
    let replay = ReplayedImportedSource::check(base, source, roots).unwrap();
    assert!(matches!(
        replay.checked_constant(&n("query")),
        Err(ReplayedSourceError::NotKernelChecked(_))
    ));
}

#[test]
fn replayed_source_stale_matcher_metadata_cannot_reuse_original_record() {
    let (base, source, roots) = fixture();
    let replay = ReplayedImportedSource::check(base, Arc::clone(&source), roots).unwrap();
    let mut changed = (*source).clone();
    let info = clean_kernel::env::MatcherInfo {
        num_params: 0,
        num_discrs: 0,
        alt_num_params: vec![],
        u_elim_pos: None,
        discr_names: vec![],
        details: None,
    };
    changed
        .register_matcher_info(n("query"), info.clone())
        .unwrap();
    assert!(source.get_matcher_info(&n("query")).is_none());
    assert_eq!(changed.get_matcher_info(&n("query")), Some(&info));
    assert_eq!(
        source.get_const(&n("query")),
        changed.get_const(&n("query"))
    );
    assert!(matches!(
        replay.require_record(&changed, &n("query")),
        Err(ReplayedSourceError::SourceChanged(_))
    ));
}

#[test]
fn replayed_source_base_axiom_does_not_check_the_original_definition_value() {
    let (base, source, roots) = fixture();
    let query = n("query");
    let original_info = source.get_const(&query).unwrap().clone();
    assert!(base.get_const(&query).is_none());
    let mut direct = (*base).clone();
    assert!(
        direct
            .add_decl(Declaration::Definition {
                name: query.clone(),
                level_params: original_info.level_params.clone(),
                type_: original_info.type_.clone(),
                value: Expr::sort(Level::zero()),
                is_reducible: false,
            })
            .is_err(),
        "the existing kernel must reject this original definition value"
    );
    let mut given = (*base).clone();
    given
        .add_decl(Declaration::Axiom {
            name: query.clone(),
            level_params: original_info.level_params.clone(),
            type_: original_info.type_.clone(),
        })
        .unwrap();
    let mut changed = (*source).clone();
    let mut invalid = original_info;
    invalid.value = Some(Expr::sort(Level::zero()));
    changed.forget_decl(&query);
    assert!(changed
        .extend_constants_structural(std::iter::once(invalid))
        .is_empty());
    changed.set_constant_origin(
        query.clone(),
        ConstantOrigin::olean_import(Some("UncheckedValue".into())),
    );
    let replay = ReplayedImportedSource::check(Arc::new(given), Arc::new(changed), roots).unwrap();
    assert!(
        replay.verdict().passed(false),
        "logical replay over the base axiom is permitted"
    );
    assert!(replay
        .checked_environment()
        .get_const(&query)
        .unwrap()
        .value
        .is_none());
    assert!(replay
        .original_environment()
        .get_const(&query)
        .unwrap()
        .value
        .is_some());
    assert!(
        matches!(
            replay.checked_constant(&query),
            Err(ReplayedSourceError::NotKernelChecked(_))
        ),
        "a fully checked base axiom must not attest an unchecked original definition value"
    );
}

#[test]
fn replayed_source_identical_fully_checked_base_definition_preserves_source_eligibility() {
    let (base, source, roots) = fixture();
    let query = n("query");
    let info = source.get_const(&query).unwrap().clone();
    let mut given = (*base).clone();
    given
        .add_decl(Declaration::Definition {
            name: query.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: info.value.clone().unwrap(),
            is_reducible: false,
        })
        .unwrap();
    let replay =
        ReplayedImportedSource::check(Arc::new(given), Arc::clone(&source), roots).unwrap();
    assert_eq!(replay.checked_constant(&query).unwrap().value, info.value);
    assert!(source.constant_needs_recheck(&query));
}

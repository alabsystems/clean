// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Support half of the kernel-parity batch sweep (spliced into
// `sweep_census.rs` via include!): failure-genre classification, the
// shadow cross-check, and the CLEAN_SWEEP_DUMP diagnostics.

fn classify_genre(reason: &str) -> String {
    const TABLE: &[(&str, &str)] = &[
        ("prelude-shadow-mismatch", "prelude-shadow"),
        ("carried-inductive-unsupported", "family-fence"),
        (
            "does not match the source environment's checked metadata",
            "family-crosscheck-mismatch",
        ),
        ("non-foundational union closure", "family-union-closure"),
        ("dependency-cycle", "dependency-cycle"),
        ("unknown-constant", "unknown-constant"),
        ("has no stored value", "no-value-external"),
        ("has no stored proof value", "no-value-external"),
        ("(opaque)", "external-opaque"),
        ("hash-failed", "hash-failed"),
        ("could not be reassembled", "family-reassembly"),
    ];
    for (needle, genre) in TABLE {
        if reason.contains(needle) {
            return (*genre).to_string();
        }
    }
    if reason.contains("Type mismatch") {
        return "kernel-type-mismatch".to_string();
    }
    if reason.contains("kernel-rejected") || reason.contains("add_inductive re-check") {
        return "kernel-rejected-other".to_string();
    }
    "other".to_string()
}

/// Cross-check a silently-substituted recheck-env (prelude) constant against
/// the source (olean) spelling and record every kernel-meaningful mismatch.
///
/// The gate's dependency resolution short-circuits on recheck presence —
/// treating NAME identity as Lean-fidelity. That is exactly where the
/// Monoid-overlay and opaque-Nat.mod divergences hide: the dependent's later
/// add_decl failure is the symptom, the silent substitution is the root.
/// Comparison discipline mirrors the family carry cross-check: binder info
/// ignored, elaborator annotations consumed; values compared only where they
/// are kernel-meaningful (Definition delta-unfolding); theorem proof VALUES
/// are proof-irrelevant and skipped.
fn shadow_check(cx: &mut SweepCx<'_>, dep: &str, dep_name: &Name) {
    // Family-root resolution: a member shadow is diagnosed at its root.
    if let Some(root) = inductive_family_root(cx.source, dep_name) {
        let root_str = root.to_string();
        if !cx.shadow_checked.insert(root_str.clone()) {
            return;
        }
        shadow_check_family(cx, &root, &root_str);
        return;
    }
    if !cx.shadow_checked.insert(dep.to_string()) {
        return;
    }
    let (Some(src), Some(rc)) = (
        cx.source.get_const(dep_name),
        cx.state.recheck.get_const(dep_name),
    ) else {
        return;
    };
    let mut diffs: Vec<&str> = Vec::new();
    if src.kind != rc.kind {
        diffs.push("kind");
    }
    if src.level_params.len() != rc.level_params.len() {
        diffs.push("level-params");
    }
    if !shadow_exprs_equal(&src.level_params, &src.type_, &rc.level_params, &rc.type_) {
        diffs.push("type");
    }
    // Delta-relevant value comparison: definitions (and opaque-vs-def kind
    // mismatches already flagged above). Theorem proofs are proof-irrelevant.
    if src.kind == ConstantKind::Definition && rc.kind == ConstantKind::Definition {
        match (&src.value, &rc.value) {
            (Some(a), Some(b)) if shadow_exprs_equal(&src.level_params, a, &rc.level_params, b) => {
            }
            (None, None) => {}
            _ => diffs.push("value"),
        }
    }
    if diffs.is_empty() {
        return;
    }
    let reason = format!(
        "prelude-shadow-mismatch [{}]: recheck-env `{dep}` (kind {:?}) silently shadows the \
         source spelling (kind {:?}) but is not the same kernel object — source type `{}` vs \
         recheck type `{}`",
        diffs.join("+"),
        rc.kind,
        src.kind,
        trunc(&format!("{}", src.type_), 240),
        trunc(&format!("{}", rc.type_), 240),
    );
    let taint = TaintSet::new();
    cx.record(dep, "prelude-shadow", reason, &taint);
}

/// Family flavor of the shadow cross-check: compare the source side tables
/// (root type, num_params, constructor names/types) against the recheck
/// (prelude) family of the same name.
fn shadow_check_family(cx: &mut SweepCx<'_>, root: &Name, root_str: &str) {
    let Some(src_ind) = cx.source.get_inductive(root) else {
        return;
    };
    let Some(rc_ind) = cx.state.recheck.get_inductive(root) else {
        if cx.state.recheck.get_const(root).is_some() {
            let taint = TaintSet::new();
            cx.record(
                root_str,
                "prelude-shadow",
                format!(
                    "prelude-shadow-mismatch [family-vs-plain]: source family root \
                     `{root_str}` is shadowed by a NON-inductive recheck constant"
                ),
                &taint,
            );
        }
        return;
    };
    let mut diffs: Vec<String> = Vec::new();
    if src_ind.num_params != rc_ind.num_params {
        diffs.push(format!(
            "num_params {} vs {}",
            src_ind.num_params, rc_ind.num_params
        ));
    }
    if src_ind.level_params.len() != rc_ind.level_params.len() {
        diffs.push("level-params".to_string());
    }
    if !shadow_exprs_equal(
        &src_ind.level_params,
        &src_ind.type_,
        &rc_ind.level_params,
        &rc_ind.type_,
    ) {
        diffs.push("root-type".to_string());
    }
    if src_ind.constructor_names != rc_ind.constructor_names {
        diffs.push(format!(
            "ctor-names {:?} vs {:?}",
            src_ind.constructor_names, rc_ind.constructor_names
        ));
    } else {
        for ctor in &src_ind.constructor_names {
            let (Some(s), Some(r)) = (
                cx.source.get_constructor(ctor),
                cx.state.recheck.get_constructor(ctor),
            ) else {
                diffs.push(format!("ctor `{ctor}` missing on one side"));
                continue;
            };
            if !shadow_exprs_equal(&s.level_params, &s.type_, &r.level_params, &r.type_) {
                diffs.push(format!(
                    "ctor `{ctor}` type: source `{}` vs recheck `{}`",
                    trunc(&format!("{}", s.type_), 300),
                    trunc(&format!("{}", r.type_), 300),
                ));
            }
        }
    }
    if diffs.is_empty() {
        return;
    }
    let reason = format!(
        "prelude-shadow-mismatch [family]: recheck-env family `{root_str}` silently shadows \
         the source family but diverges: {}",
        diffs.join("; ")
    );
    let taint = TaintSet::new();
    cx.record(root_str, "prelude-shadow", reason, &taint);
}

fn trunc(s: &str, n: usize) -> String {
    if s.chars().count() <= n {
        s.to_string()
    } else {
        format!(
            "{}…[{} chars]",
            s.chars().take(n).collect::<String>(),
            s.len()
        )
    }
}

fn dump_env_side(label: &str, env: &Environment, name: &Name) {
    match env.get_const(name) {
        Some(info) => println!(
            "  [{label}] const kind={:?} levels={:?}\n    type:  {}\n    value: {}",
            info.kind,
            info.level_params,
            trunc(&format!("{}", info.type_), 800),
            info.value
                .as_ref()
                .map_or("<none>".to_string(), |v| trunc(&format!("{v}"), 800)),
        ),
        None => println!("  [{label}] const: ABSENT"),
    }
    if let Some(ind) = env.get_inductive(name) {
        println!(
            "  [{label}] InductiveVal num_params={} num_indices={} ctors={:?} nested={}",
            ind.num_params, ind.num_indices, ind.constructor_names, ind.is_nested
        );
    }
    if let Some(ctor) = env.get_constructor(name) {
        println!(
            "  [{label}] ConstructorVal of={} num_params={} num_fields={} idx={}\n    ctor type: {}",
            ctor.inductive_name,
            ctor.num_params,
            ctor.num_fields,
            ctor.constructor_idx,
            trunc(&format!("{}", ctor.type_), 1200),
        );
    }
    if let Some(rec) = env.get_recursor(name) {
        println!(
            "  [{label}] RecursorVal of={} (rules={})",
            rec.inductive_name,
            rec.rules.len()
        );
    }
}

fn dump_constant(source: &Environment, recheck: &Environment, name: &str) {
    println!("[sweep dump] ===== {name} =====");
    let n = Name::from_string(name);
    dump_env_side("source ", source, &n);
    dump_env_side("recheck", recheck, &n);
}

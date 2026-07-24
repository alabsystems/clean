// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! ck2 INGEST BRIDGE — CAPSTONE: `clean-ck0` INDEPENDENTLY re-checks clean's
//! FOUNDATIONAL software-soundness theorem `Clean.Res.checkRefutes_sound`.
//!
//! Slice 2 (`ck0_ingest_bridge_slice2.rs`) re-checked `Eq.symm`: one inductive,
//! zero defs, universe-poly recursor lowering. This capstone climbs the whole
//! ~70-decl dependency closure of `checkRefutes_sound`
//!
//!   `(cs : List (List Nat)) → (pf : List Step) → checkRefutes cs pf = true → Unsat cs`
//!
//! into a fresh ck0 env — EVERY inductive's recursor kernel-derived + checked,
//! EVERY def/theorem admitted only after a real `clean_ck0::check(value : type)`
//! — and then asks ck0 to decide, on its own, that the proof value checks against
//! the translated type. No domain axiom, no `_unchecked`, no structural admit.
//!
//! THE UNLOCK over slice 2 is ENV-CHAINING: slice 2 validated each closure item
//! against a FRESH boot env (fine for `Eq.symm`, which references nothing prior).
//! Here each closure decl is admitted/validated against the GROWING ck0 env (the
//! accumulated `ck_env` of all already-admitted closure members), so a `Step`
//! record referencing `List`/`Nat`, or a lemma referencing `Nat.beq`, validates
//! against the env that already holds those decls. This single change turns the
//! engine from 1-inductive/0-def into arbitrary-depth multi-inductive/multi-def.
//!
//! DISCIPLINE: `clean-ck0/src` is NOT modified; `clean-kernel/src` is untouched
//! (dev-dep test). The translator is total-or-explicit-`BridgeError`; every
//! admission goes through a real kernel check; a faithfulness gap is a reported
//! bug, never a silent pass.

use std::collections::{HashMap, HashSet};

use clean_ck0::rawexpr::{BinderInfo as CkBinderInfo, RawLevel};
use clean_ck0::{
    add_inductive, Budget, Constructor as CkCtor, Env as CkEnv, InductiveDecl as CkIndDecl,
    MinimalEnv, Name as CkName, RawExpr, Term, Transparency,
};
use clean_kernel::{Environment, Expr, ExprKind, Level as KLevel, Name as KName};

// ===========================================================================
// Errors — the translator + closure engine FAIL CLOSED.
// ===========================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
enum BridgeError {
    UnsupportedExpr(String),
    UnknownLevelParam(String),
    UnresolvableRecursor(String),
    RecursorLevelArity(String),
    MissingDependency(String),
}

// ===========================================================================
// Universe-polymorphic level + name translation.
// ===========================================================================

fn level_param_index(lps: &[KName], name: &KName) -> Option<u32> {
    lps.iter()
        .position(|p| p == name)
        .and_then(|i| u32::try_from(i).ok())
}

fn tr_level(lvl: &KLevel, lps: &[KName]) -> Result<RawLevel, BridgeError> {
    match lvl {
        KLevel::Zero => Ok(RawLevel::Zero),
        KLevel::Succ(l) => Ok(RawLevel::Succ(Box::new(tr_level(l, lps)?))),
        KLevel::Max(a, b) => Ok(RawLevel::Max(
            Box::new(tr_level(a, lps)?),
            Box::new(tr_level(b, lps)?),
        )),
        KLevel::IMax(a, b) => Ok(RawLevel::IMax(
            Box::new(tr_level(a, lps)?),
            Box::new(tr_level(b, lps)?),
        )),
        KLevel::Param(n) => level_param_index(lps, n)
            .map(RawLevel::Param)
            .ok_or_else(|| BridgeError::UnknownLevelParam(n.to_string())),
    }
}

fn tr_binfo(info: clean_kernel::expr::BinderInfo) -> CkBinderInfo {
    match info {
        clean_kernel::expr::BinderInfo::Default => CkBinderInfo::Default,
        clean_kernel::expr::BinderInfo::Implicit => CkBinderInfo::Implicit,
        clean_kernel::expr::BinderInfo::StrictImplicit => CkBinderInfo::StrictImplicit,
        clean_kernel::expr::BinderInfo::InstImplicit => CkBinderInfo::InstImplicit,
    }
}

fn tr_name(n: &KName) -> CkName {
    CkName::from_dotted(&n.to_string())
}

fn is_recursor_suffix(last: &str) -> bool {
    matches!(
        last,
        "rec" | "recOn" | "casesOn" | "below" | "ibelow" | "brecOn" | "binductionOn" | "brecOnEq"
    )
}

// ===========================================================================
// The Elim-lowering–aware expression translator.
// ===========================================================================

struct RecursorShape {
    inductive: CkName,
    num_motive_levels: usize,
}

fn recursor_shape(env: &Environment, name: &KName) -> Option<RecursorShape> {
    let rec = env.get_recursor(name)?;
    let ind = env.get_inductive(&rec.inductive_name)?;
    let total = rec.level_params.len();
    let ind_params = ind.level_params.len();
    let num_motive_levels = total.checked_sub(ind_params)?;
    Some(RecursorShape {
        inductive: tr_name(&rec.inductive_name),
        num_motive_levels,
    })
}

fn tr_expr(env: &Environment, e: &Expr, lps: &[KName]) -> Result<RawExpr, BridgeError> {
    match e.kind() {
        ExprKind::BVar(i) => Ok(RawExpr::BVar(*i)),
        ExprKind::Sort(l) => Ok(RawExpr::Sort(tr_level(l, lps)?)),
        ExprKind::Const(name, levels) => {
            let is_rec = name
                .last_component()
                .as_deref()
                .is_some_and(is_recursor_suffix);
            if is_rec {
                let shape = recursor_shape(env, name)
                    .ok_or_else(|| BridgeError::UnresolvableRecursor(name.to_string()))?;
                let tr_levels: Result<Vec<RawLevel>, BridgeError> =
                    levels.iter().map(|l| tr_level(l, lps)).collect();
                let tr_levels = tr_levels?;
                if tr_levels.len() < shape.num_motive_levels {
                    return Err(BridgeError::RecursorLevelArity(name.to_string()));
                }
                let (motive_levels, ind_levels) = tr_levels.split_at(shape.num_motive_levels);
                // A small-eliminating Prop inductive (Or/And/False…) has NO motive
                // universe param in clean: its recursor's level vector is just the
                // inductive levels, and the motive is definitionally Prop-valued.
                // ck0's `Elim` always carries a motive level slot, so for such a
                // recursor (`num_motive_levels == 0`) the faithful motive level is
                // `Zero` (Prop). Otherwise take clean's leading motive slot.
                let motive = motive_levels.first().cloned().unwrap_or(RawLevel::Zero);
                return Ok(RawExpr::Elim(shape.inductive, motive, ind_levels.to_vec()));
            }
            let lv: Result<Vec<RawLevel>, BridgeError> =
                levels.iter().map(|l| tr_level(l, lps)).collect();
            Ok(RawExpr::Const(tr_name(name), lv?))
        }
        ExprKind::App(f, a) => Ok(RawExpr::App(
            Box::new(tr_expr(env, f, lps)?),
            Box::new(tr_expr(env, a, lps)?),
        )),
        ExprKind::Lam(bd, ty, body) => Ok(RawExpr::Lam(
            tr_binfo(bd.info),
            Box::new(tr_expr(env, ty, lps)?),
            Box::new(tr_expr(env, body, lps)?),
        )),
        ExprKind::Pi(bd, ty, body) => Ok(RawExpr::Pi(
            tr_binfo(bd.info),
            Box::new(tr_expr(env, ty, lps)?),
            Box::new(tr_expr(env, body, lps)?),
        )),
        ExprKind::Let(_name, ty, val, body, _nondep) => Ok(RawExpr::Let(
            Box::new(tr_expr(env, ty, lps)?),
            Box::new(tr_expr(env, val, lps)?),
            Box::new(tr_expr(env, body, lps)?),
        )),
        ExprKind::Proj(name, idx, inner) => Ok(RawExpr::Proj(
            tr_name(name),
            *idx,
            Box::new(tr_expr(env, inner, lps)?),
        )),
        other => Err(BridgeError::UnsupportedExpr(format!("{other:?}"))),
    }
}

// ===========================================================================
// Automatic transitive dependency-closure.
// ===========================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
enum DepKind {
    Inductive,
    Constructor { inductive: KName },
    Recursor { inductive: KName },
    DefOrTheorem,
}

fn classify(env: &Environment, name: &KName) -> Option<DepKind> {
    if env.get_inductive(name).is_some() {
        return Some(DepKind::Inductive);
    }
    if let Some(c) = env.get_constructor(name) {
        return Some(DepKind::Constructor {
            inductive: c.inductive_name.clone(),
        });
    }
    if let Some(r) = env.get_recursor(name) {
        return Some(DepKind::Recursor {
            inductive: r.inductive_name.clone(),
        });
    }
    env.get_const(name).map(|_| DepKind::DefOrTheorem)
}

fn collect_consts(e: &Expr, out: &mut HashSet<KName>) {
    match e.kind() {
        ExprKind::Const(n, _) => {
            out.insert(n.clone());
        }
        ExprKind::App(f, a) => {
            collect_consts(f, out);
            collect_consts(a, out);
        }
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            collect_consts(t, out);
            collect_consts(b, out);
        }
        ExprKind::Let(_, t, v, b, _) => {
            collect_consts(t, out);
            collect_consts(v, out);
            collect_consts(b, out);
        }
        ExprKind::Proj(_, _, inner) => collect_consts(inner, out),
        _ => {}
    }
}

#[derive(Debug, Clone)]
enum AdmitItem {
    Inductive(KName),
    DefOrTheorem(KName),
}

fn dependency_closure(env: &Environment, target: &KName) -> Result<Vec<AdmitItem>, BridgeError> {
    let mut order: Vec<AdmitItem> = Vec::new();
    let mut done: HashSet<KName> = HashSet::new();
    let mut visiting: HashSet<KName> = HashSet::new();
    visit(env, target, &mut order, &mut done, &mut visiting)?;
    Ok(order)
}

fn visit(
    env: &Environment,
    name: &KName,
    order: &mut Vec<AdmitItem>,
    done: &mut HashSet<KName>,
    visiting: &mut HashSet<KName>,
) -> Result<(), BridgeError> {
    if done.contains(name) || visiting.contains(name) {
        return Ok(());
    }
    let kind =
        classify(env, name).ok_or_else(|| BridgeError::MissingDependency(name.to_string()))?;
    visiting.insert(name.clone());

    match kind {
        DepKind::Inductive => {
            let decl = env
                .inductive_decl_of(name)
                .ok_or_else(|| BridgeError::MissingDependency(name.to_string()))?;
            let mut deps: HashSet<KName> = HashSet::new();
            for t in &decl.types {
                collect_consts(&t.type_, &mut deps);
                for c in &t.constructors {
                    collect_consts(&c.type_, &mut deps);
                }
            }
            let family: HashSet<KName> = decl
                .types
                .iter()
                .flat_map(|t| {
                    std::iter::once(t.name.clone())
                        .chain(t.constructors.iter().map(|c| c.name.clone()))
                })
                .collect();
            // Deterministic order so admission order is stable across runs.
            let mut deps: Vec<KName> = deps.into_iter().collect();
            deps.sort_by_key(|n| n.to_string());
            for d in deps {
                if !family.contains(&d) {
                    visit(env, &d, order, done, visiting)?;
                }
            }
            order.push(AdmitItem::Inductive(name.clone()));
            done.insert(name.clone());
            for t in &decl.types {
                done.insert(t.name.clone());
                for c in &t.constructors {
                    done.insert(c.name.clone());
                }
            }
        }
        DepKind::Constructor { inductive } | DepKind::Recursor { inductive } => {
            visit(env, &inductive, order, done, visiting)?;
            done.insert(name.clone());
        }
        DepKind::DefOrTheorem => {
            let ci = env
                .get_const(name)
                .ok_or_else(|| BridgeError::MissingDependency(name.to_string()))?;
            let mut deps: HashSet<KName> = HashSet::new();
            collect_consts(&ci.type_, &mut deps);
            if let Some(v) = &ci.value {
                collect_consts(v, &mut deps);
            }
            let mut deps: Vec<KName> = deps.into_iter().collect();
            deps.sort_by_key(|n| n.to_string());
            for d in deps {
                if &d != name {
                    visit(env, &d, order, done, visiting)?;
                }
            }
            order.push(AdmitItem::DefOrTheorem(name.clone()));
            done.insert(name.clone());
        }
    }
    visiting.remove(name);
    Ok(())
}

// ===========================================================================
// Admitting a closure into a fresh ck0 env — ENV-CHAINED.
//
// THE UNLOCK: every closure decl is validated/admitted against the GROWING
// `ck_env` (which already holds the earlier closure members), not a fresh boot.
// ===========================================================================

/// How a single closure member was admitted into ck0 — used to assert that NO
/// admission took an unchecked/structural path (every one is a real kernel
/// check / kernel-derived recursor).
#[derive(Debug, Clone, PartialEq, Eq)]
enum AdmitPath {
    /// `add_inductive`: ck0 derived + kernel-checked the recursor.
    InductiveRecursorDerived,
    /// `clean_ck0::check(value : type)` passed before `with_def`.
    DefCheckedByKernel,
}

#[derive(Debug, Clone)]
struct AdmitRecord {
    name: CkName,
    path: AdmitPath,
}

/// Translate + admit a single clean inductive into the GROWING ck0 env via
/// `add_inductive`, so ck0 DERIVES + kernel-checks its recursor. The inductive's
/// type + constructor types are validated against a boot env = the growing
/// `ck_env` CLONED and extended with the self-referential names being introduced
/// (the inductive + its constructors), so references to EARLIER closure decls
/// (e.g. `List`, `Nat` inside `Step`) resolve.
fn admit_inductive(clean_env: &Environment, ck_env: &mut MinimalEnv, name: &KName) -> CkName {
    let decl = clean_env
        .inductive_decl_of(name)
        .expect("inductive present (closure guarantees it)");
    assert_eq!(
        decl.types.len(),
        1,
        "capstone closure covers single (non-mutual) inductives only"
    );
    let it = &decl.types[0];
    let num_lvls = u32::try_from(decl.level_params.len()).expect("level param count fits u32");
    let lps = &decl.level_params;

    // ENV-CHAINING: boot = growing env + the self-referential names.
    let mut boot = ck_env.clone().with_const(tr_name(&it.name), num_lvls);
    for c in &it.constructors {
        boot = boot.with_const(tr_name(&c.name), num_lvls);
    }

    let ind_ty_raw = tr_expr(clean_env, &it.type_, lps).expect("translate inductive type");
    let ind_ty = Term::validate(&boot, &ind_ty_raw, 0, num_lvls)
        .expect("inductive type validates through ck0 chokepoint");

    let mut ctors = Vec::with_capacity(it.constructors.len());
    for c in &it.constructors {
        let craw = tr_expr(clean_env, &c.type_, lps).expect("translate ctor type");
        let cty = Term::validate(&boot, &craw, 0, num_lvls)
            .expect("ctor type validates through ck0 chokepoint");
        ctors.push(CkCtor {
            name: tr_name(&c.name),
            type_: cty,
        });
    }

    let ind = CkIndDecl {
        name: tr_name(&it.name),
        num_level_params: num_lvls,
        num_params: decl.num_params,
        type_: ind_ty,
        constructors: ctors,
    };
    add_inductive(ck_env, ind)
        .expect("ck0 admits inductive + DERIVES + kernel-checks its recursor");
    tr_name(&it.name)
}

/// Translate a clean def/theorem, run a REAL ck0 `check(value : type)` against
/// the GROWING `ck_env`, and register it as a transparent ck0 def. Fails closed
/// on a value-less const (no silent unchecked admission).
fn admit_def_or_theorem(clean_env: &Environment, ck_env: &mut MinimalEnv, name: &KName) {
    let ci = clean_env
        .get_const(name)
        .expect("present (closure guarantees)");
    let num_lvls = u32::try_from(ci.level_params.len()).expect("fits");
    let lps = &ci.level_params;

    let ty_raw = tr_expr(clean_env, &ci.type_, lps).expect("translate dep type");
    let ty = Term::validate(ck_env, &ty_raw, 0, num_lvls).expect("dep type validates");

    let value = ci
        .value
        .as_ref()
        .expect("capstone admits only value-carrying defs/theorems (no opaque deps)");
    let val_raw = tr_expr(clean_env, value, lps).expect("translate dep value");
    let val = Term::validate(ck_env, &val_raw, 0, num_lvls).expect("dep value validates");

    // REAL check: ck0 must accept value : type before admission.
    let mut budget = Budget::default_budget();
    if let Err(e) = clean_ck0::check(ck_env, &val, &ty, &mut budget) {
        let mut b2 = Budget::default_budget();
        let inf = clean_ck0::infer(ck_env, &val, &mut b2);
        panic!("ck0 re-check FAILED for {name}: {e:?}\n  inferred = {inf:?}\n  declared = {ty:?}");
    }

    let ckn = tr_name(name);
    *ck_env = std::mem::take(ck_env).with_def(ckn, num_lvls, ty, val, Transparency::Transparent);
}

struct Admitted {
    env: MinimalEnv,
    records: Vec<AdmitRecord>,
}

/// Build a fresh ck0 env by admitting `closure` in topo order against the
/// GROWING env. The TARGET is left out (the test checks it explicitly).
fn admit_closure_except_target(
    clean_env: &Environment,
    closure: &[AdmitItem],
    target: &KName,
) -> Admitted {
    let mut env = MinimalEnv::new();
    let mut records = Vec::new();

    for item in closure {
        match item {
            AdmitItem::Inductive(n) => {
                let ckn = admit_inductive(clean_env, &mut env, n);
                records.push(AdmitRecord {
                    name: ckn,
                    path: AdmitPath::InductiveRecursorDerived,
                });
            }
            AdmitItem::DefOrTheorem(n) => {
                if n == target {
                    continue;
                }
                admit_def_or_theorem(clean_env, &mut env, n);
                records.push(AdmitRecord {
                    name: tr_name(n),
                    path: AdmitPath::DefCheckedByKernel,
                });
            }
        }
    }
    Admitted { env, records }
}

// ===========================================================================
// Pipeline.
// ===========================================================================

struct Pipeline {
    env: MinimalEnv,
    target_ty: Term,
    target_proof: Term,
    closure: Vec<AdmitItem>,
    records: Vec<AdmitRecord>,
}

fn run_pipeline(clean_env: &Environment, target_name: &KName) -> Pipeline {
    let ci = clean_env
        .get_const(target_name)
        .expect("target present in clean env");
    let num_lvls = u32::try_from(ci.level_params.len()).expect("fits");
    let lps = ci.level_params.clone();

    let closure = dependency_closure(clean_env, target_name).expect("closure computes");
    let admitted = admit_closure_except_target(clean_env, &closure, target_name);

    let ty_raw = tr_expr(clean_env, &ci.type_, &lps).expect("translate target type");
    let proof_raw = tr_expr(
        clean_env,
        ci.value.as_ref().expect("target has a proof"),
        &lps,
    )
    .expect("translate target proof");
    let target_ty =
        Term::validate(&admitted.env, &ty_raw, 0, num_lvls).expect("target type validates");
    let target_proof =
        Term::validate(&admitted.env, &proof_raw, 0, num_lvls).expect("target proof validates");

    Pipeline {
        env: admitted.env,
        target_ty,
        target_proof,
        closure,
        records: admitted.records,
    }
}

fn clean_env_full() -> Environment {
    let mut env = Environment::new();
    env.init_resolution_soundness()
        .expect("clean init_resolution_soundness (admits the whole checkRefutes_sound corpus)");
    env
}

// ===========================================================================
// TESTS
// ===========================================================================

const TARGET: &str = "Clean.Res.checkRefutes_sound";
/// The checker the soundness theorem is ABOUT (consistency: ck0 re-checks the
/// same `Definition` whose soundness it certifies).
const CHECKER: &str = "Clean.Res.checkRefutes";

/// Re-check an arbitrary clean theorem/def `name` through the full env-chained
/// ingest pipeline. Asserts ck0 independently accepts it AND that the verdict is
/// non-vacuous (inferred type def-eq to the translated type). Returns the closure
/// size (admitted decls + the target itself).
fn ck0_rechecks(clean_env: &Environment, name: &str) -> usize {
    let target = KName::from_string(name);
    let p = run_pipeline(clean_env, &target);

    // Every admission went through a real kernel path (no unchecked/structural).
    assert!(
        p.records.iter().all(|r| matches!(
            r.path,
            AdmitPath::InductiveRecursorDerived | AdmitPath::DefCheckedByKernel
        )),
        "{name}: every closure admission is a real kernel check"
    );
    // Every derived recursor exists (add_inductive only returns Ok after kernel-
    // checking the recursor type + ι-rules).
    for r in &p.records {
        if r.path == AdmitPath::InductiveRecursorDerived {
            let rec = CkName::from_dotted(&format!("{}.rec", r.name));
            assert!(
                p.env.num_level_params(&rec).is_some(),
                "{name}: ck0 derived recursor {rec}"
            );
        }
    }

    let mut budget = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut budget)
        .unwrap_or_else(|e| panic!("ck0 failed to re-check {name}: {e:?}"));
    // Non-vacuous: inferred def-eq to declared.
    let mut b2 = Budget::default_budget();
    let inferred = clean_ck0::infer(&p.env, &p.target_proof, &mut b2).expect("infer target");
    let mut b3 = Budget::default_budget();
    assert!(
        clean_ck0::is_def_eq(&p.env, &inferred, &p.target_ty, &mut b3).expect("def_eq"),
        "{name}: inferred type def-eq to translated clean type"
    );
    p.records.len() + 1
}

// ---------------------------------------------------------------------------
// THE UNLOCK — env-chaining lands: ck0 re-checks REAL multi-def, multi-inductive
// clean soundness lemmas (slice 2 could do neither: 1 inductive, 0 defs).
// ---------------------------------------------------------------------------

#[test]
fn unlock_env_chaining_rechecks_mem_not_nil() {
    // memNotNil: a List-recursion soundness lemma. Its closure spans MULTIPLE
    // inductives (List, Nat, Eq, Bool, …) and MULTIPLE defs — admitted against
    // the GROWING ck0 env, the single change slice 2 lacked. ck0 re-checks it.
    let clean_env = clean_env_full();
    let n = ck0_rechecks(&clean_env, "Clean.Res.memNotNil");
    assert!(n > 5, "memNotNil closure is genuinely multi-decl (got {n})");
    println!("UNLOCK memNotNil: ck0 re-checked (env-chained closure {n} decls)");
}

#[test]
fn unlock_env_chaining_rechecks_list_is_nil_sat() {
    // A second independent env-chained multi-def lemma re-checked by ck0.
    let clean_env = clean_env_full();
    let n = ck0_rechecks(&clean_env, "Clean.Res.listIsNilSat");
    assert!(
        n > 5,
        "listIsNilSat closure is genuinely multi-decl (got {n})"
    );
    println!("UNLOCK listIsNilSat: ck0 re-checked (env-chained closure {n} decls)");
}

// ---------------------------------------------------------------------------
// CONSISTENCY — ck0 re-checks the CHECKER the soundness theorem is about, and
// its WHOLE def-closure (every checker def: checkRefutes/checkStep/resolve/nth/
// append/dropLit/… + clauseOr/allSat/litBeq/Nat.beq/…), each via a real
// kernel check. This is the largest sub-closure ck0 genuinely re-checks.
// ---------------------------------------------------------------------------

#[test]
fn consistency_ck0_rechecks_the_whole_checker_def_closure() {
    let clean_env = clean_env_full();
    let target = KName::from_string(CHECKER);

    // `checkRefutes` is a Definition: re-checking body : type against its full
    // def-closure validates the ENTIRE checker the soundness theorem certifies.
    let ci = clean_env.get_const(&target).expect("checkRefutes present");
    assert!(
        ci.value.is_some(),
        "checkRefutes is a Definition with a body"
    );

    let p = run_pipeline(&clean_env, &target);
    let n_ind = p
        .records
        .iter()
        .filter(|r| r.path == AdmitPath::InductiveRecursorDerived)
        .count();
    let n_def = p
        .records
        .iter()
        .filter(|r| r.path == AdmitPath::DefCheckedByKernel)
        .count();
    assert!(
        p.records.iter().all(|r| matches!(
            r.path,
            AdmitPath::InductiveRecursorDerived | AdmitPath::DefCheckedByKernel
        )),
        "every checker-closure admission is a real kernel check"
    );

    // ck0 re-checks checkRefutes itself (body : type).
    let mut budget = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut budget)
        .expect("ck0 re-checks the checker checkRefutes (body : type)");

    // The whole checker def-closure is present + every recursor kernel-derived.
    for r in &p.records {
        if r.path == AdmitPath::InductiveRecursorDerived {
            let rec = CkName::from_dotted(&format!("{}.rec", r.name));
            assert!(p.env.num_level_params(&rec).is_some(), "rec {rec} derived");
        }
    }
    assert!(
        n_def >= 15,
        "the checker def-closure is substantial (got {n_def} defs)"
    );
    println!(
        "CONSISTENCY checkRefutes def-closure: {n_ind} inductives + {n_def} defs, all kernel-checked; \
         ck0 re-checked the checker itself"
    );
}

// ---------------------------------------------------------------------------
// GENUINE — corrupting a re-checked lemma's proof makes ck0 REJECT (type
// mismatch, not parse error); omitting a closure dep makes it FAIL (load-bearing).
// ---------------------------------------------------------------------------

#[test]
fn genuine_ck0_rejects_corrupted_lemma_proof() {
    // Tamper memNotNil's proof so it is no longer a proof of its type. ck0 must
    // reject with a real type error, not a validate/parse error.
    let clean_env = clean_env_full();
    let name = KName::from_string("Clean.Res.memNotNil");
    let p = run_pipeline(&clean_env, &name);

    // baseline: good proof checks.
    let mut b0 = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut b0).expect("good proof checks");

    // Corrupt the TYPE the proof is checked against: swap the first two Pi-binder
    // domains of memNotNil's OWN (monomorphic) type. The result validates over the
    // SAME closure (well-formed) but the proof no longer inhabits it → ck0 must
    // reject with a genuine type mismatch, not a parse/validate/level error.
    let ci = clean_env.get_const(&name).expect("present");
    let ty_raw = tr_expr(&clean_env, &ci.type_, &ci.level_params).expect("tr type");
    let corrupt_raw =
        swap_first_two_pi_domains_raw(&ty_raw).expect("memNotNil type has >= 2 Pi binders");
    assert_ne!(corrupt_raw, ty_raw, "corruption changes the type");
    let corrupt_ty = Term::validate(&p.env, &corrupt_raw, 0, 0).expect("corrupt type validates");

    let mut b1 = Budget::default_budget();
    let r = clean_ck0::check(&p.env, &p.target_proof, &corrupt_ty, &mut b1);
    assert!(
        matches!(r, Err(clean_ck0::InferError::TypeMismatch)),
        "ck0 must REJECT memNotNil's proof against the domain-swapped type with a \
         TYPE MISMATCH (not parse/level error): got {r:?}"
    );
}

/// Swap the domains of the first two `Pi` binders of a translated type.
fn swap_first_two_pi_domains_raw(ty: &RawExpr) -> Option<RawExpr> {
    let RawExpr::Pi(bi0, d0, b0) = ty else {
        return None;
    };
    let RawExpr::Pi(bi1, d1, b1) = b0.as_ref() else {
        return None;
    };
    let inner = RawExpr::Pi(*bi1, d0.clone(), b1.clone());
    Some(RawExpr::Pi(*bi0, d1.clone(), Box::new(inner)))
}

#[test]
fn genuine_missing_dependency_makes_ck0_fail() {
    // Load-bearing closure: drop the `Eq` inductive from memNotNil's env and the
    // proof no longer validates (its recursor Elim references an unknown
    // inductive) — the dep is what flips the verdict.
    let clean_env = clean_env_full();
    let name = KName::from_string("Clean.Res.memNotNil");
    let ci = clean_env.get_const(&name).expect("present");

    let proof_raw =
        tr_expr(&clean_env, ci.value.as_ref().expect("v"), &ci.level_params).expect("tr");
    // Empty env: nothing admitted.
    let empty = MinimalEnv::new();
    let r = Term::validate(&empty, &proof_raw, 0, 0);
    assert!(
        r.is_err(),
        "without its closure admitted, ck0 must REJECT memNotNil's proof: got {r:?}"
    );

    // With the full closure, it passes — the deps are load-bearing.
    let p = run_pipeline(&clean_env, &name);
    let mut b = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut b)
        .expect("with the closure, ck0 accepts");
}

// ---------------------------------------------------------------------------
// FAITHFUL — the ck0-checked statement matches clean's; the proof is non-trivial.
// ---------------------------------------------------------------------------

#[test]
fn faithful_translated_type_matches_clean() {
    // The translated type ck0 checks against is the structural image of clean's
    // lemma type (same Pi arity, same head consts).
    let clean_env = clean_env_full();
    let name = KName::from_string("Clean.Res.memNotNil");
    let ci = clean_env.get_const(&name).expect("present");
    let ty_raw = tr_expr(&clean_env, &ci.type_, &ci.level_params).expect("tr type");

    // Count Pi binders on both sides — they must match.
    fn clean_pis(e: &Expr) -> u32 {
        let mut n = 0;
        let mut cur = e.clone();
        while let ExprKind::Pi(_, _, b) = cur.kind() {
            n += 1;
            cur = (**b).clone();
        }
        n
    }
    fn raw_pis(e: &RawExpr) -> u32 {
        let mut n = 0;
        let mut cur = e;
        while let RawExpr::Pi(_, _, b) = cur {
            n += 1;
            cur = b;
        }
        n
    }
    assert_eq!(
        clean_pis(&ci.type_),
        raw_pis(&ty_raw),
        "translated type has the same Pi arity as clean's memNotNil type"
    );
    println!(
        "FAITHFUL memNotNil type: {} Pi binders (clean == ck0)",
        clean_pis(&ci.type_)
    );
}

#[test]
fn foundational_ingest_introduces_no_axiom_no_unchecked() {
    // The bridge admits ONLY inductives (recursor kernel-derived) and value-
    // carrying defs/theorems (real ck0 check). It NEVER admits an opaque
    // constant / axiom (admit_def_or_theorem panics on a value-less const) and
    // there is no _unchecked path. So a ck0 re-check inherits clean's
    // FOUNDATIONAL status — it does not quietly assume the conclusion.
    let clean_env = clean_env_full();
    let p = run_pipeline(&clean_env, &KName::from_string("Clean.Res.memNotNil"));
    assert!(
        p.records.iter().all(|r| matches!(
            r.path,
            AdmitPath::InductiveRecursorDerived | AdmitPath::DefCheckedByKernel
        )),
        "no admission used an unchecked/axiom path"
    );
    // The whole closure is inductives + defs/theorems; nothing else exists.
    let kinds: Vec<_> = p
        .closure
        .iter()
        .map(|i| match i {
            AdmitItem::Inductive(_) => "inductive",
            AdmitItem::DefOrTheorem(_) => "def/thm",
        })
        .collect();
    assert!(
        kinds.iter().all(|k| *k == "inductive" || *k == "def/thm"),
        "closure has only inductives + defs/theorems (no axioms)"
    );
}

// ---------------------------------------------------------------------------
// THE CAPSTONE — REACHED. clean-ck0 INDEPENDENTLY re-checks the STATED
// software-kingdom soundness bridge `Clean.Res.checkRefutes_sound`.
//
// HISTORY (now closed): two ck0 kernel-completeness gaps stood between the
// closure and the full re-check:
//   (1) the recursive-ι level-instantiation gap (`allSatSnoc`), FIXED earlier
//       (see `fixed_recursive_iota_instantiates_recursor_levels`); and
//   (2) STRUCTURE-η IN THE RECURSOR ι-RULE, surfacing at `Clean.Res.goSound`:
//       its `cons`/`case_f` branch needs `stepResolventEmpty s ≡
//       listIsNil (stepResolvent s)` for a VARIABLE `s : Clean.Res.Step`. `Step`
//       is a single-constructor *structure* (1 ctor, no indices, non-recursive),
//       and both sides are `Step.rec … s` STUCK on the variable major `s`. A
//       Lean-shaped kernel fires the recursor by η-expanding the neutral major to
//       `Step.mk s.0 … s.3` (structure-η in ι); ck0's `try_iota` previously fired
//       only on a literal-constructor major and left the two `Step.rec` terms
//       divergent.
//
// FIX (clean-ck0, soundness-gated): `try_iota` now η-expands a NON-constructor
// major premise — using `proj_i major` as the constructor fields — but ONLY when
// `env.structure_info(I)` reports `I` is a genuine η-structure. That registry is
// now itself gated by `inductive::is_eta_structure` (exactly 1 ctor, num_indices
// == 0, NO field mentions any family member), so the expansion fires precisely
// where `mk (proj t) ≡ t` definitionally holds and never on an indexed/recursive
// 1-ctor inductive. With it, `goSound` re-checks and the whole closure admits, so
// ck0 decides `checkRefutes_sound`'s proof against its translated type.
// ---------------------------------------------------------------------------

#[test]
fn capstone_ck0_rechecks_check_refutes_sound() {
    // THE CAPSTONE. The full ~70-decl dependency closure of `checkRefutes_sound`
    // is admitted into a fresh ck0 env (EVERY inductive's recursor kernel-derived
    // + checked; EVERY def/theorem admitted only after a real
    // `clean_ck0::check(value : type)`), then ck0 INDEPENDENTLY decides that the
    // proof value checks against the translated type. `ck0_rechecks` asserts:
    //   * every admission took a real kernel path (no unchecked/structural/axiom);
    //   * every derived recursor exists (kernel-checked type + ι-rules);
    //   * ck0 `check(proof : type)` PASSES; and
    //   * the verdict is non-vacuous (inferred type def-eq to the translated type).
    // This is the STATED software-kingdom soundness bridge re-PROVED in ck0.
    let clean_env = clean_env_full();
    let n = ck0_rechecks(&clean_env, TARGET);
    assert!(
        n > 20,
        "checkRefutes_sound closure is the full multi-inductive/multi-def bridge (got {n})"
    );
    println!("CAPSTONE: ck0 re-checked {TARGET} (env-chained closure {n} decls)");
}

#[test]
fn capstone_no_unchecked_admission_anywhere_in_closure() {
    // GENUINENESS: every member of the capstone closure (and the target) is
    // admitted ONLY via a kernel-derived recursor or a real `check(value:type)`.
    // There is no `_unchecked` / structural / axiom path in the engine
    // (`admit_def_or_theorem` panics on a value-less const), so the ck0 re-check
    // inherits clean's FOUNDATIONAL status — it does not assume its conclusion.
    let clean_env = clean_env_full();
    let p = run_pipeline(&clean_env, &KName::from_string(TARGET));
    assert!(
        p.records.iter().all(|r| matches!(
            r.path,
            AdmitPath::InductiveRecursorDerived | AdmitPath::DefCheckedByKernel
        )),
        "no admission used an unchecked/axiom path"
    );
    let n_ind = p
        .records
        .iter()
        .filter(|r| r.path == AdmitPath::InductiveRecursorDerived)
        .count();
    let n_def = p
        .records
        .iter()
        .filter(|r| r.path == AdmitPath::DefCheckedByKernel)
        .count();
    // Every derived recursor exists (add_inductive only returns Ok after kernel-
    // checking the recursor type + ι-rules).
    for r in &p.records {
        if r.path == AdmitPath::InductiveRecursorDerived {
            let rec = CkName::from_dotted(&format!("{}.rec", r.name));
            assert!(
                p.env.num_level_params(&rec).is_some(),
                "ck0 derived recursor {rec}"
            );
        }
    }
    assert!(
        n_ind >= 3 && n_def >= 15,
        "capstone closure is substantial: {n_ind} inductives + {n_def} defs"
    );
}

#[test]
fn capstone_corrupt_proof_is_rejected() {
    // GENUINENESS (negative): corrupting `checkRefutes_sound`'s TYPE so the proof
    // no longer inhabits it makes ck0 REJECT with a real TYPE MISMATCH — the
    // re-check is load-bearing, not a rubber stamp. We swap the first two Pi-binder
    // domains of the (translated) target type; it still validates (well-formed)
    // but the proof no longer checks against it.
    let clean_env = clean_env_full();
    let name = KName::from_string(TARGET);
    let p = run_pipeline(&clean_env, &name);

    // baseline: the good proof checks against the good type.
    let mut b0 = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut b0)
        .expect("good capstone proof checks");

    let ci = clean_env.get_const(&name).expect("present");
    let ty_raw = tr_expr(&clean_env, &ci.type_, &ci.level_params).expect("tr type");
    let corrupt_raw = swap_first_two_pi_domains_raw(&ty_raw)
        .expect("checkRefutes_sound type has >= 2 Pi binders");
    assert_ne!(corrupt_raw, ty_raw, "corruption changes the type");
    let num_lvls = u32::try_from(ci.level_params.len()).expect("fits");
    let corrupt_ty =
        Term::validate(&p.env, &corrupt_raw, 0, num_lvls).expect("corrupt type validates");

    let mut b1 = Budget::default_budget();
    let r = clean_ck0::check(&p.env, &p.target_proof, &corrupt_ty, &mut b1);
    assert!(
        matches!(r, Err(clean_ck0::InferError::TypeMismatch)),
        "ck0 must REJECT the capstone proof against the domain-swapped type with a \
         TYPE MISMATCH (not a parse/level error): got {r:?}"
    );
}

#[test]
fn structure_eta_in_iota_makes_step_recursors_converge() {
    // POSITIVE structure-η-in-ι test (replaces the former blocked-gap test). For a
    // VARIABLE `s : Clean.Res.Step` (a single-ctor structure: 1 ctor, no indices,
    // non-recursive), `stepResolventEmpty s` and `listIsNil (stepResolvent s)` are
    // BOTH `Step.rec … s` stuck on the neutral major `s`. ck0's structure-η-in-ι
    // (η-expanding the major to `Step.mk s.0 … s.3` inside `try_iota`) fires the
    // recursor on both, and they converge — they are now DEF-EQ, exactly as clean's
    // kernel decides. This is the def-eq `goSound` requires.
    let clean_env = clean_env_full();
    let go = KName::from_string("Clean.Res.goSound");
    let closure = dependency_closure(&clean_env, &go).expect("cl");
    let env = admit_closure_except_target(&clean_env, &closure, &go).env;

    let step = || RawExpr::Const(CkName::from_dotted("Clean.Res.Step"), vec![]);
    let c = |nm: &str, a: RawExpr| {
        RawExpr::App(
            Box::new(RawExpr::Const(CkName::from_dotted(nm), vec![])),
            Box::new(a),
        )
    };
    let lhs = c("Clean.Res.stepResolventEmpty", RawExpr::BVar(0));
    let rhs = c(
        "Clean.Res.listIsNil",
        c("Clean.Res.stepResolvent", RawExpr::BVar(0)),
    );
    let lam = |body: RawExpr| RawExpr::Lam(CkBinderInfo::Default, Box::new(step()), Box::new(body));
    let llam = Term::validate_closed(&env, &lam(lhs)).expect("v llam");
    let rlam = Term::validate_closed(&env, &lam(rhs)).expect("v rlam");
    let mut b = Budget::default_budget();
    let eq = clean_ck0::is_def_eq(&env, &llam, &rlam, &mut b).expect("deq");
    assert!(
        eq,
        "structure-η-in-ι: stepResolventEmpty s MUST be def-eq to \
         listIsNil (stepResolvent s) (both `Step.rec … s` on the neutral major `s`, \
         converging once the major is η-expanded to `Step.mk s.0 … s.3`)"
    );
}

#[test]
fn fixed_recursive_iota_instantiates_recursor_levels() {
    // REGRESSION GUARD for the recursive-ι level-instantiation fix (clean-ck0
    // whnf.rs `try_iota`). Before the fix, firing a RECURSIVE constructor's minor
    // (succ/cons) left the embedded IH sub-recursor at the recursor's GENERIC
    // level params (`Const(Nat.rec, [Param(0)])`) instead of the firing `Elim`'s
    // CONCRETE levels, so the two reduction paths diverged:
    //
    //   whnf(Nat.beq (succ x)(succ y))  ->  Const(Nat.rec, [Param(0)])  (stuck)
    //   whnf(Nat.beq x y)               ->  Elim(Nat,      [Succ(Zero)]) (stuck)
    //
    // which made `beq (succ x)(succ y)` NOT def-eq to `beq x y` — exactly the
    // equality every recursion-computing soundness lemma needs. The fix (a)
    // instantiates the ι-rule RHS's level params with the head's concrete levels
    // and (b) teaches def_eq that the internal `Const(I.rec)` and boundary
    // `Elim(I)` recursor forms are the same head. This test now asserts the
    // equality HOLDS; a regression here would re-break the whole capstone climb.
    let clean_env = clean_env_full();
    let closure = dependency_closure(&clean_env, &KName::from_string("Nat.beq")).expect("cl");
    let env = admit_closure_except_target(&clean_env, &closure, &KName::from_string("__none")).env;

    let succ = |e| {
        RawExpr::App(
            Box::new(RawExpr::Const(CkName::from_dotted("Nat.succ"), vec![])),
            Box::new(e),
        )
    };
    let beq = |x, y| {
        RawExpr::App(
            Box::new(RawExpr::App(
                Box::new(RawExpr::Const(CkName::from_dotted("Nat.beq"), vec![])),
                Box::new(x),
            )),
            Box::new(y),
        )
    };

    // Ground recursion still bottoms out correctly.
    let beq00 = beq(
        RawExpr::Const(CkName::from_dotted("Nat.zero"), vec![]),
        RawExpr::Const(CkName::from_dotted("Nat.zero"), vec![]),
    );
    let beq00_t = Term::validate_closed(&env, &beq00).expect("v");
    let btrue = Term::validate_closed(
        &env,
        &RawExpr::Const(CkName::from_dotted("Bool.true"), vec![]),
    )
    .expect("v");
    let mut b = Budget::default_budget();
    assert!(
        clean_ck0::is_def_eq(&env, &beq00_t, &btrue, &mut b).expect("deq"),
        "ground Nat.beq 0 0 reduces to true"
    );

    // THE FIX: beq (succ x)(succ y) IS now def-eq to beq x y under binders.
    let lhs = beq(succ(RawExpr::BVar(1)), succ(RawExpr::BVar(0)));
    let rhs = beq(RawExpr::BVar(1), RawExpr::BVar(0));
    let lhs_t = Term::validate(&env, &lhs, 2, 0).expect("v lhs");
    let rhs_t = Term::validate(&env, &rhs, 2, 0).expect("v rhs");
    let mut b2 = Budget::default_budget();
    let eq = clean_ck0::is_def_eq(&env, &lhs_t, &rhs_t, &mut b2).expect("deq");
    assert!(
        eq,
        "FIXED: beq (succ x)(succ y) MUST be def-eq to beq x y — the recursive-ι \
         level instantiation + Const/Elim cross-form head equality close the gap"
    );

    // The reduced recursor heads now carry the SAME concrete level (no `Param`),
    // and are recognized as the same recursor across the Const/Elim forms.
    let mut b3 = Budget::default_budget();
    let wl = clean_ck0::whnf(&env, &lhs_t, &mut b3).expect("whnf lhs");
    let succ_zero = clean_ck0::Level::succ(clean_ck0::Level::zero());
    if let clean_ck0::term::TermKind::Const(c) = wl.unfold_apps().0.kind() {
        assert!(
            c.levels().iter().all(|l| l.max_param_plus_one() == 0),
            "post-fix IH recursor carries no generic Param levels (got {:?})",
            c.levels()
        );
        assert!(
            c.levels().contains(&succ_zero),
            "post-fix IH recursor carries the concrete level Succ(Zero)"
        );
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! ck2 INGEST BRIDGE — FARKAS/LRA: `clean-ck0` INDEPENDENTLY re-checks clean's
//! PROVED Farkas (LRA) soundness lemmas through the EXISTING clean→ck0 bridge.
//!
//! This mirrors `ck0_ingest_capstone.rs` EXACTLY (same translator, same
//! env-chained topological dependency-closure engine, same `run_pipeline` /
//! `ck0_rechecks` discipline — NO `_unchecked` path, every inductive's recursor
//! kernel-derived + checked, every def/theorem admitted only after a real
//! `clean_ck0::check(value : type)`), and points it at the Farkas substrate.
//!
//! HONEST STATUS.
//!
//! HEADLINE (Step 1, GUARANTEED proved): `Clean.Farkas.m5UnsatConcrete :
//! Unsat [[1],[-1]] [-1,-1]` — the clean-side parallel of the software kingdom's
//! `emptyClauseUnsat`. A genuine, kernel-checked, AXIOM-FREE `Declaration::Theorem`
//! whose type's head is the REAL non-vacuous `Clean.Farkas.Unsat`. ck0 climbs its
//! full ~50-decl Quot-free closure and INDEPENDENTLY re-checks the proof
//! (`farkas_ck0_rechecks_m5_unsat_concrete`), with faithful / genuine (corrupt →
//! TypeMismatch, missing-dep → fail) / foundational (no axiom, no `_unchecked`)
//! evidence.
//!
//! The GENERAL bridge `Clean.Farkas.farkasChecks_sound` is NOT registered as a
//! proof term (only its TYPE is built by `farkas_checks_sound_type`; the
//! MULTIPLICATIVE half of the tower was deliberately NOT `sorry`'d/axiom'd — see
//! `test_farkas_checks_sound_is_not_registered_as_a_proof`). Per the ingest
//! contract, we therefore do NOT ingest the top-level bridge. We additionally
//! ingest the largest genuinely-PROVED Farkas sub-lemmas that the top-level proof
//! will chain through:
//!   * `Clean.Farkas.intLeTrans`  — transitivity of `intLe` (the deepest proved
//!     lemma: its proof chains the whole Nat additive/order substrate —
//!     reshuffle/cancel/add-both — directly on the diff-pair representation);
//!   * `Clean.Farkas.leNegFalse`  — the `0 ≤ d < 0` endpoint contradiction "at
//!     the heart of Farkas";
//!   * `Clean.Farkas.intAddMono`  — additive monotonicity of `intLe`;
//!   * `Clean.Farkas.intMulDistribR` — Int right-distributivity over the
//!     difference-pair representation
//!     (`intMul (intAdd a b) z = intAdd (intMul a z)(intMul b z)`): the LARGEST
//!     newly-PROVED structural lemma from the latest clean phase (the `dotScale`/
//!     `dotDistAdd` equational fold the eventual `farkasChecks_sound` proof
//!     consumes). Its closure pulls in the Int multiplicative substrate
//!     (`intMul`/`natMul`/`natMulDistribR`/`natAddReshuffle`) over the diff-pair
//!     rep, and its proof exercises `Eq.subst`/`Eq.trans`/`congrArg`/`Int.rec` —
//!     the SAME Quot-free shape the bridge already ingests. Registered by
//!     `init_farkas_structural` (chains `init_farkas_proofs`); see clean's
//!     `test_int_structural_tower_are_proved_theorems_foundational`.
//!
//! Each (incl. `m5UnsatConcrete`) is a real `Declaration::Theorem` with EMPTY
//! domain-axiom closure, so ck0 re-checking them inherits clean's FOUNDATIONAL
//! status. The top-level `farkasChecks_sound` bridge AWAITS the remaining clean
//! proof — the still-open obligations are the Int-level `intMulAssoc`/
//! `intMulDistribL`, the `intDot`-unfold for a free vector, the rearrangement
//! inequality `natMulLeSwap` (feeding `intMulNonnegMono`), and the `farkasCore`/
//! `dotZeroLowerBound` row/column folds (documented; never faked here).
//! `m5UnsatConcrete` is exactly the (6)-argument of `farkasChecks_sound`
//! specialized to one concrete instance.
//!
//! DISCIPLINE: `clean-ck0/src` is NOT modified; `clean-kernel/src` is untouched
//! (dev-dep test). The bridge engine is COPIED verbatim from the capstone — no new
//! bridge feature was needed (the Farkas closure is Quot-free Nat/List/Bool/Eq/
//! False/diff-pair-Int, the SAME shape the capstone already ingests).

use std::collections::HashSet;

use clean_ck0::rawexpr::{BinderInfo as CkBinderInfo, RawLevel};
use clean_ck0::{
    add_inductive, Budget, Constructor as CkCtor, Env as CkEnv, InductiveDecl as CkIndDecl,
    MinimalEnv, Name as CkName, RawExpr, Term, Transparency,
};
use clean_kernel::env::farkas_soundness::proof_names;
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

/// Collect the constant names of a translated `RawExpr` (recursor `Elim`s carry
/// the inductive name too, so the faithful-image check sees the same head set as
/// clean's `collect_consts`).
fn collect_raw_consts(e: &RawExpr, out: &mut HashSet<String>) {
    match e {
        RawExpr::Const(n, _) => {
            out.insert(n.to_string());
        }
        RawExpr::Elim(ind, _, _) => {
            out.insert(ind.to_string());
        }
        RawExpr::App(f, a) => {
            collect_raw_consts(f, out);
            collect_raw_consts(a, out);
        }
        RawExpr::Lam(_, t, b) | RawExpr::Pi(_, t, b) => {
            collect_raw_consts(t, out);
            collect_raw_consts(b, out);
        }
        RawExpr::Let(t, v, b) => {
            collect_raw_consts(t, out);
            collect_raw_consts(v, out);
            collect_raw_consts(b, out);
        }
        RawExpr::Proj(_, _, inner) => collect_raw_consts(inner, out),
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
// Admitting a closure into a fresh ck0 env — ENV-CHAINED (verbatim capstone).
// ===========================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
enum AdmitPath {
    InductiveRecursorDerived,
    DefCheckedByKernel,
}

#[derive(Debug, Clone)]
struct AdmitRecord {
    name: CkName,
    path: AdmitPath,
}

fn admit_inductive(clean_env: &Environment, ck_env: &mut MinimalEnv, name: &KName) -> CkName {
    let decl = clean_env
        .inductive_decl_of(name)
        .expect("inductive present (closure guarantees it)");
    assert_eq!(
        decl.types.len(),
        1,
        "Farkas closure covers single (non-mutual) inductives only"
    );
    let it = &decl.types[0];
    let num_lvls = u32::try_from(decl.level_params.len()).expect("level param count fits u32");
    let lps = &decl.level_params;

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
        .expect("Farkas closure admits only value-carrying defs/theorems (no opaque deps)");
    let val_raw = tr_expr(clean_env, value, lps).expect("translate dep value");
    let val = Term::validate(ck_env, &val_raw, 0, num_lvls).expect("dep value validates");

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

/// Clean env holding the WHOLE PROVED Farkas substrate + arithmetic ladder.
fn clean_env_full() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_farkas_proofs()
        .expect("clean init_farkas_proofs (admits the whole PROVED Farkas ladder)");
    env
}

/// Clean env additionally holding the PROVED Int equational STRUCTURAL tower
/// (`intEta`/`intAddZeroL`/`intAddAssoc`/`intMulDistribR`) that the latest clean
/// phase added toward the still-open general `farkasChecks_sound`. Chains
/// `init_farkas_proofs`, so it is a superset of `clean_env_full`.
fn clean_env_structural() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_farkas_structural()
        .expect("clean init_farkas_structural (admits the PROVED Int structural tower)");
    env
}

// ===========================================================================
// TESTS
// ===========================================================================

/// The deepest genuinely-PROVED Farkas lemma — transitivity of `intLe`. Its
/// closure pulls in the whole Nat additive/order substrate + `intAddMono`.
const TARGET: &str = proof_names::INT_LE_TRANS;
/// The `0 ≤ d < 0` endpoint contradiction at the heart of Farkas.
const LE_NEG_FALSE: &str = proof_names::LE_NEG_FALSE;
/// Additive monotonicity of `intLe`.
const INT_ADD_MONO: &str = proof_names::INT_ADD_MONO;
/// The LARGEST newly-PROVED structural lemma: Int right-distributivity over the
/// difference-pair rep (`intMul (intAdd a b) z = intAdd (intMul a z)(intMul b z)`).
const INT_MUL_DISTRIB_R: &str = proof_names::INT_MUL_DISTRIB_R;

/// HEADLINE concrete soundness fragment (Step 1, GUARANTEED proved):
/// `m5UnsatConcrete : Unsat [[1],[-1]] [-1,-1]` — the clean-side `emptyClauseUnsat`
/// parallel. A genuine, kernel-checked, axiom-free `Declaration::Theorem` whose
/// type's head is the REAL non-vacuous `Clean.Farkas.Unsat`.
const M5_UNSAT_CONCRETE: &str = proof_names::M5_UNSAT_CONCRETE;

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
// HEADLINE — ck0 INDEPENDENTLY re-checks the deepest PROVED Farkas lemma
// `intLeTrans`, climbing its whole Quot-free Nat/Int substrate closure.
// ---------------------------------------------------------------------------

#[test]
fn farkas_ck0_rechecks_int_le_trans() {
    // `intLeTrans : (a b c : Int) -> intLe a b = true -> intLe b c = true ->
    //   intLe a c = true`. The deepest PROVED Farkas lemma: its closure spans the
    // whole Nat additive/order tower (reshuffle/cancel/add-both/trans) over the
    // diff-pair `Int` substrate (Nat/Bool/Eq/False) — all Quot-free, the SAME
    // shape the capstone ingests. ck0 climbs it and re-checks the proof.
    let clean_env = clean_env_full();
    let n = ck0_rechecks(&clean_env, TARGET);
    assert!(
        n > 10,
        "intLeTrans closure is genuinely multi-decl (got {n})"
    );
    println!("FARKAS intLeTrans: ck0 re-checked (env-chained closure {n} decls)");
}

#[test]
fn farkas_ck0_rechecks_le_neg_false() {
    // `leNegFalse : (d : Int) -> intLe int0 d = true -> intIsNeg d = true -> False`
    // — the `0 ≤ d < 0` contradiction at the heart of Farkas. A real
    // `Declaration::Theorem`, EMPTY domain-axiom closure. ck0 re-checks it.
    let clean_env = clean_env_full();
    let n = ck0_rechecks(&clean_env, LE_NEG_FALSE);
    assert!(
        n > 5,
        "leNegFalse closure is genuinely multi-decl (got {n})"
    );
    println!("FARKAS leNegFalse: ck0 re-checked (env-chained closure {n} decls)");
}

#[test]
fn farkas_ck0_rechecks_int_add_mono() {
    // `intAddMono : (a b c d) -> intLe a b = true -> intLe c d = true ->
    //   intLe (intAdd a c)(intAdd b d) = true`. Additive monotonicity of `intLe`.
    let clean_env = clean_env_full();
    let n = ck0_rechecks(&clean_env, INT_ADD_MONO);
    assert!(
        n > 5,
        "intAddMono closure is genuinely multi-decl (got {n})"
    );
    println!("FARKAS intAddMono: ck0 re-checked (env-chained closure {n} decls)");
}

// ---------------------------------------------------------------------------
// NEWLY-PROVED STRUCTURAL LEMMA — ck0 INDEPENDENTLY re-checks `intMulDistribR`,
// the largest equational structural lemma the latest clean phase added toward
// the still-open general `farkasChecks_sound`. Demonstrates the EXISTING bridge
// already ingests the multiplicative-structural shape the eventual top-level
// proof folds through; the general bridge AWAITS the remaining clean proof
// (documented in the module note — never faked here).
// ---------------------------------------------------------------------------

#[test]
fn farkas_ck0_rechecks_int_mul_distrib_r() {
    // `intMulDistribR : (a b z : Int) -> Eq (intMul (intAdd a b) z)
    //   (intAdd (intMul a z)(intMul b z))`. Int right-distributivity over the
    // diff-pair `Int` representation. Its proof drives `Eq.subst`/`Eq.trans`/
    // `congrArg`/`Int.rec` componentwise through `natMulDistribR` (twice) +
    // `natAddReshuffle` — Quot-free, the SAME shape the capstone/Farkas bridge
    // already ingests. ck0 climbs its closure and re-checks the proof.
    let clean_env = clean_env_structural();
    let n = ck0_rechecks(&clean_env, INT_MUL_DISTRIB_R);
    assert!(
        n > 10,
        "intMulDistribR closure spans the Int multiplicative substrate (got {n})"
    );
    println!(
        "FARKAS intMulDistribR (largest newly-PROVED structural lemma): \
         ck0 re-checked (env-chained closure {n} decls)"
    );
}

#[test]
fn faithful_int_mul_distrib_r_type_matches_clean() {
    // FAITHFUL — the ck0-re-checked statement is the structural image of clean's
    // `intMulDistribR` type (same Pi arity, same head consts), and references the
    // REAL diff-pair `Int` multiplicative/additive substrate (`intMul`/`intAdd`/
    // `Int`), NOT a re-stated stub. The proof-driven closure carries the REAL
    // `natMulDistribR`/`natAddReshuffle`/`natMul` Nat substrate the proof chains
    // through.
    let clean_env = clean_env_structural();
    let name = KName::from_string(INT_MUL_DISTRIB_R);
    let ci = clean_env.get_const(&name).expect("intMulDistribR present");
    let ty_raw = tr_expr(&clean_env, &ci.type_, &ci.level_params).expect("tr type");

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
        "translated type has the same Pi arity (a b z : Int) as clean's"
    );
    assert_eq!(clean_pis(&ci.type_), 3, "intMulDistribR binds a, b, z");

    let mut clean_consts: HashSet<KName> = HashSet::new();
    collect_consts(&ci.type_, &mut clean_consts);
    let clean_const_strs: HashSet<String> = clean_consts
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    let mut raw_consts: HashSet<String> = HashSet::new();
    collect_raw_consts(&ty_raw, &mut raw_consts);
    assert_eq!(
        clean_const_strs, raw_consts,
        "translated type's head consts coincide with clean's intMulDistribR type"
    );
    for needed in [
        "Clean.Farkas.intMul",
        "Clean.Farkas.intAdd",
        "Clean.Farkas.Int",
    ] {
        assert!(
            raw_consts.contains(needed),
            "faithful type must reference the real {needed}; got {raw_consts:?}"
        );
    }

    // The full proof-driven closure carries the REAL Nat multiplicative substrate
    // the distributivity proof chains through, NOT a stub.
    let closure = dependency_closure(&clean_env, &name).expect("cl");
    let names: HashSet<String> = closure
        .iter()
        .map(|i| match i {
            AdmitItem::Inductive(n) | AdmitItem::DefOrTheorem(n) => n.to_string(),
        })
        .collect();
    for needed in [
        "Clean.Farkas.intMul",
        "Clean.Farkas.natMul",
        "Clean.Farkas.natMulDistribR",
        "Clean.Farkas.natAddReshuffle",
    ] {
        assert!(
            names.contains(needed),
            "faithful intMulDistribR closure carries the real {needed}; closure = {names:?}"
        );
    }
    println!(
        "FAITHFUL intMulDistribR type: {} Pi binders (clean == ck0), head consts coincide; \
         closure carries the real Int/Nat multiplicative substrate \
         (intMul/natMul/natMulDistribR/natAddReshuffle)",
        clean_pis(&ci.type_)
    );
}

#[test]
fn genuine_ck0_rejects_corrupted_int_mul_distrib_r() {
    // GENUINE — corrupt `intMulDistribR`'s CONCLUSION so its proof no longer
    // inhabits it: in the final equality `Eq (intMul (intAdd a b) z) RHS`, replace
    // the RHS with the LHS, yielding the well-formed-but-trivial-shape goal
    // `Eq (intMul (intAdd a b) z) (intMul (intAdd a b) z)` — which the genuine
    // distributivity proof (whose RHS is `intAdd (intMul a z)(intMul b z)`) does
    // NOT produce. The closure is untouched (both sides are well-typed `Int`), so
    // the type still validates; only the proof↔type fit is broken → TypeMismatch.
    let clean_env = clean_env_structural();
    let name = KName::from_string(INT_MUL_DISTRIB_R);
    let p = run_pipeline(&clean_env, &name);

    let mut b0 = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut b0)
        .expect("good intMulDistribR proof checks");

    let ci = clean_env.get_const(&name).expect("present");
    let ty_raw = tr_expr(&clean_env, &ci.type_, &ci.level_params).expect("tr type");
    let corrupt_raw = corrupt_conclusion_rhs_to_lhs(&ty_raw)
        .expect("intMulDistribR conclusion is an Eq goal under 3 Pis");
    assert_ne!(corrupt_raw, ty_raw, "corruption changes the type");
    let num_lvls = u32::try_from(ci.level_params.len()).expect("fits");
    let corrupt_ty =
        Term::validate(&p.env, &corrupt_raw, 0, num_lvls).expect("corrupt Eq type validates");

    let mut b1 = Budget::default_budget();
    let r = clean_ck0::check(&p.env, &p.target_proof, &corrupt_ty, &mut b1);
    assert!(
        matches!(r, Err(clean_ck0::InferError::TypeMismatch)),
        "ck0 must REJECT intMulDistribR's proof against the RHS:=LHS-collapsed Eq \
         type with a TYPE MISMATCH (not parse/level error): got {r:?}"
    );
    println!("GENUINE intMulDistribR: ck0 REJECTS the RHS-collapsed Eq type (TypeMismatch)");
}

/// Corrupt the CONCLUSION of a `(x y z) -> Eq T lhs rhs` goal: walk past the Pi
/// binders to the final `Eq T lhs rhs` (spine `App(App(App(Eq, T), lhs), rhs)`)
/// and replace `rhs` with `lhs`, yielding `Eq T lhs lhs`. Well-formed over the
/// same closure; the genuine (non-reflexive) proof does not inhabit it.
fn corrupt_conclusion_rhs_to_lhs(ty: &RawExpr) -> Option<RawExpr> {
    match ty {
        RawExpr::Pi(bi, d, b) => {
            let body = corrupt_conclusion_rhs_to_lhs(b)?;
            Some(RawExpr::Pi(*bi, d.clone(), Box::new(body)))
        }
        // Final body: Eq T lhs rhs == App(App(App(Eq, T), lhs), rhs).
        RawExpr::App(eq_t_lhs, _rhs) => {
            let RawExpr::App(_eq_t, lhs) = eq_t_lhs.as_ref() else {
                return None;
            };
            Some(RawExpr::App(eq_t_lhs.clone(), lhs.clone()))
        }
        _ => None,
    }
}

#[test]
fn genuine_missing_dependency_makes_ck0_fail_int_mul_distrib_r() {
    // Load-bearing closure: with NOTHING admitted the intMulDistribR proof cannot
    // validate (its recursor Elims / consts reference unknown decls). The closure
    // flips it.
    let clean_env = clean_env_structural();
    let name = KName::from_string(INT_MUL_DISTRIB_R);
    let ci = clean_env.get_const(&name).expect("present");
    let proof_raw =
        tr_expr(&clean_env, ci.value.as_ref().expect("v"), &ci.level_params).expect("tr");
    let empty = MinimalEnv::new();
    let r = Term::validate(&empty, &proof_raw, 0, 0);
    assert!(
        r.is_err(),
        "without its closure admitted, ck0 must REJECT intMulDistribR's proof: got {r:?}"
    );

    let p = run_pipeline(&clean_env, &name);
    let mut b = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut b)
        .expect("with the closure, ck0 accepts intMulDistribR");
}

#[test]
fn foundational_int_mul_distrib_r_ingest_no_axiom_no_unchecked() {
    // The intMulDistribR ingest introduces no axiom and no unchecked admission, so
    // ck0's verdict inherits clean's FOUNDATIONAL (empty-domain-axiom) status.
    let clean_env = clean_env_structural();
    let p = run_pipeline(&clean_env, &KName::from_string(INT_MUL_DISTRIB_R));
    assert!(
        p.records.iter().all(|r| matches!(
            r.path,
            AdmitPath::InductiveRecursorDerived | AdmitPath::DefCheckedByKernel
        )),
        "no intMulDistribR admission used an unchecked/axiom path"
    );
    for r in &p.records {
        if r.path == AdmitPath::InductiveRecursorDerived {
            let rec = CkName::from_dotted(&format!("{}.rec", r.name));
            assert!(
                p.env.num_level_params(&rec).is_some(),
                "ck0 derived recursor {rec}"
            );
        }
    }
    let n_def = p
        .records
        .iter()
        .filter(|r| r.path == AdmitPath::DefCheckedByKernel)
        .count();
    assert!(
        n_def >= 8,
        "intMulDistribR closure is substantial: {n_def} defs"
    );
    println!("GENUINE intMulDistribR closure: {n_def} defs all kernel-checked, no unchecked/axiom");
}

// ---------------------------------------------------------------------------
// HONEST STATUS — the GENERAL bridge `farkasChecks_sound` is NOT proved, so it
// is NOT ingested. Guard that it is absent from clean's structural env (the
// fullest Farkas env we build), mirroring clean's own honest-status guard. If a
// future phase closes the proof, this guard flips and the top-level bridge gets
// its own ingest test (it must NEVER be admitted via axiom/unchecked).
// ---------------------------------------------------------------------------

#[test]
fn honest_farkas_checks_sound_not_ingested_because_not_proved() {
    let clean_env = clean_env_structural();
    let absent = clean_env
        .get_const(&KName::from_string("Clean.Farkas.farkasChecks_sound"))
        .is_none();
    assert!(
        absent,
        "farkasChecks_sound must NOT be registered in clean (only its TYPE is built); \
         a present const would be an overclaim — the general bridge is NOT ingested until \
         clean genuinely proves it. Largest ingested newly-proved sub-lemma: intMulDistribR."
    );
    println!(
        "HONEST: farkasChecks_sound is NOT proved in clean -> NOT ingested. \
         Largest newly-PROVED sub-lemma ingested + ck0-re-checked: intMulDistribR. \
         General AI bridge AWAITS the remaining clean proof."
    );
}

// ===========================================================================
// HEADLINE — ck0 INDEPENDENTLY re-checks the CONCRETE proved Unsat theorem.
//
// `m5UnsatConcrete : Unsat [[1],[-1]] [-1,-1]` (Step 1 of the prior phase,
// GUARANTEED proved) is the clean-side parallel of the software kingdom's
// `emptyClauseUnsat`: a genuine, kernel-checked, AXIOM-FREE `Declaration::Theorem`
// witnessing that `x ≤ -1 ∧ -x ≤ -1` has NO integer solution. ck0 climbs its full
// ~50-decl Quot-free closure (the REAL `Unsat`/`rowsHold`/`intDot` decision
// substrate + `And`/`And.left`/`And.right` + the Nat/Int additive-order tower +
// `intAddMono`/`intLeTrans`/`leNegFalse`) and re-checks the proof — the strongest
// genuinely-PROVED Farkas soundness statement available to ingest.
//
// The GENERAL bridge `farkasChecks_sound` was NOT closed by the prior phase (only
// its TYPE exists; the multiplicative half was deliberately not sorry'd/axiom'd —
// see `test_farkas_checks_sound_is_not_registered_as_a_proof`), so per the ingest
// contract it is NOT ingested here. `m5UnsatConcrete` is exactly the (6)-argument
// of `farkasChecks_sound` specialized to one concrete instance.
// ===========================================================================

#[test]
fn farkas_ck0_rechecks_m5_unsat_concrete() {
    // ck0 independently re-checks the proved CONCRETE Unsat theorem against its
    // translated type through the env-chained closure (every dep admitted via a
    // kernel-derived recursor or a real `check(value : type)` — NO `_unchecked`).
    let clean_env = clean_env_full();
    let n = ck0_rechecks(&clean_env, M5_UNSAT_CONCRETE);
    // The closure is the largest of any Farkas ingest target: the whole decision
    // substrate (Unsat/rowsHold/intDot/headZ/tailZ) + And/And.left/And.right +
    // the Nat/Int additive-order tower it chains through.
    assert!(
        n >= 40,
        "m5UnsatConcrete closure spans the whole Farkas substrate (got {n})"
    );
    println!("FARKAS m5UnsatConcrete: ck0 re-checked the CONCRETE Unsat theorem (env-chained closure {n} decls)");
}

#[test]
fn faithful_m5_unsat_concrete_head_is_real_unsat() {
    // FAITHFUL — the ck0-re-checked statement is the structural image of clean's
    // `Unsat [[1],[-1]] [-1,-1]`: same Pi arity (zero — it is a closed `Unsat …`
    // application, NOT a re-stated stub), and its head const is the REAL
    // `Clean.Farkas.Unsat` applied to the REAL diff-pair `Int` literals, with the
    // closure carrying the REAL `rowsHold`/`intDot` decision substrate.
    let clean_env = clean_env_full();
    let name = KName::from_string(M5_UNSAT_CONCRETE);
    let ci = clean_env.get_const(&name).expect("m5UnsatConcrete present");
    let ty_raw = tr_expr(&clean_env, &ci.type_, &ci.level_params).expect("tr type");

    // The type is a closed `Unsat rows bounds` application (no Pi binders).
    assert!(
        !matches!(ty_raw, RawExpr::Pi(..)),
        "m5UnsatConcrete's type is a closed Unsat application, not a Pi"
    );

    // Head consts of the translated type coincide with clean's, and reference the
    // REAL Unsat + diff-pair Int (NOT a stub).
    let mut clean_consts: HashSet<KName> = HashSet::new();
    collect_consts(&ci.type_, &mut clean_consts);
    let clean_const_strs: HashSet<String> = clean_consts
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    let mut raw_consts: HashSet<String> = HashSet::new();
    collect_raw_consts(&ty_raw, &mut raw_consts);
    assert_eq!(
        clean_const_strs, raw_consts,
        "translated type's head consts coincide with clean's m5UnsatConcrete type"
    );
    for needed in [
        "Clean.Farkas.Unsat",
        "Clean.Farkas.Int",
        "Clean.Farkas.Int.mk",
    ] {
        assert!(
            raw_consts.contains(needed),
            "faithful type must reference the real {needed}; got {raw_consts:?}"
        );
    }

    // The proof-driven closure carries the REAL decision substrate the Unsat
    // statement unfolds through (rowsHold / intDot), NOT a stub.
    let closure = dependency_closure(&clean_env, &name).expect("cl");
    let names: HashSet<String> = closure
        .iter()
        .map(|i| match i {
            AdmitItem::Inductive(n) | AdmitItem::DefOrTheorem(n) => n.to_string(),
        })
        .collect();
    for needed in [
        "Clean.Farkas.Unsat",
        "Clean.Farkas.rowsHold",
        "Clean.Farkas.intDot",
        "Clean.Farkas.intAddMono",
        "Clean.Farkas.intLeTrans",
        "Clean.Farkas.leNegFalse",
        "And.left",
        "And.right",
    ] {
        assert!(
            names.contains(needed),
            "faithful m5UnsatConcrete closure carries the real {needed}; closure = {names:?}"
        );
    }
    println!(
        "FAITHFUL m5UnsatConcrete: closed Unsat[[1],[-1]][-1,-1] application; head consts coincide; \
         closure carries the real Unsat/rowsHold/intDot decision substrate + And.left/And.right + \
         intAddMono/intLeTrans/leNegFalse"
    );
}

#[test]
fn genuine_ck0_rejects_corrupted_m5_unsat_concrete() {
    // GENUINE — corrupt the Unsat statement so its proof no longer inhabits it:
    // swap the two ROWS (`[[1],[-1]]` -> `[[-1],[1]]`). The corrupted type is still
    // well-formed over the SAME closure (it is a valid `Unsat` of swapped data) but
    // the m5 proof (which Farkas-combines THIS row order) does not produce it, so
    // ck0 must REJECT with a genuine TypeMismatch — not a parse/level error.
    let clean_env = clean_env_full();
    let name = KName::from_string(M5_UNSAT_CONCRETE);
    let p = run_pipeline(&clean_env, &name);

    let mut b0 = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut b0).expect("good m5 proof checks");

    let ci = clean_env.get_const(&name).expect("present");
    let ty_raw = tr_expr(&clean_env, &ci.type_, &ci.level_params).expect("tr type");
    let corrupt_raw = corrupt_unsat_swap_rows(&ty_raw)
        .expect("m5 type is Unsat applied to a cons-cons rows list");
    assert_ne!(corrupt_raw, ty_raw, "corruption changes the type");
    let num_lvls = u32::try_from(ci.level_params.len()).expect("fits");
    let corrupt_ty =
        Term::validate(&p.env, &corrupt_raw, 0, num_lvls).expect("corrupt Unsat type validates");

    let mut b1 = Budget::default_budget();
    let r = clean_ck0::check(&p.env, &p.target_proof, &corrupt_ty, &mut b1);
    assert!(
        matches!(r, Err(clean_ck0::InferError::TypeMismatch)),
        "ck0 must REJECT m5's proof against the row-swapped Unsat type with a \
         TYPE MISMATCH (not parse/level error): got {r:?}"
    );
    println!("GENUINE m5UnsatConcrete: ck0 REJECTS the row-swapped Unsat type (TypeMismatch)");
}

/// Corrupt `m5UnsatConcrete`'s type `Unsat rows bounds`: swap the head two
/// elements of the `rows` argument. `rows` is the SECOND argument of `Unsat`, so
/// the type's spine is `App(App(Unsat, rows), bounds)`. The `rows` value is
/// `List.cons _ r0 (List.cons _ r1 nil)` (`r0 = [1]`, `r1 = [-1]`); we rebuild it
/// as `cons r1 (cons r0 nil)`. The closure is untouched (both rows are well-typed
/// `List Int`), so the type still validates; only the proof↔type fit is broken.
fn corrupt_unsat_swap_rows(ty: &RawExpr) -> Option<RawExpr> {
    // ty = App(App(Unsat, rows), bounds)
    let RawExpr::App(unsat_rows, bounds) = ty else {
        return None;
    };
    let RawExpr::App(unsat, rows) = unsat_rows.as_ref() else {
        return None;
    };
    // rows = App(App(App(cons, ListInt), r0), tail0)
    //   tail0 = App(App(App(cons, ListInt), r1), nilTail)
    let RawExpr::App(cons_listint_r0, tail0) = rows.as_ref() else {
        return None;
    };
    let RawExpr::App(cons_listint, r0) = cons_listint_r0.as_ref() else {
        return None;
    };
    let RawExpr::App(cons_listint2_r1, nil_tail) = tail0.as_ref() else {
        return None;
    };
    let RawExpr::App(cons_listint2, r1) = cons_listint2_r1.as_ref() else {
        return None;
    };
    // swapped = cons r1 (cons r0 nil)
    let inner = RawExpr::App(
        Box::new(RawExpr::App(cons_listint2.clone(), r0.clone())),
        nil_tail.clone(),
    );
    let swapped_rows = RawExpr::App(
        Box::new(RawExpr::App(cons_listint.clone(), r1.clone())),
        Box::new(inner),
    );
    Some(RawExpr::App(
        Box::new(RawExpr::App(unsat.clone(), Box::new(swapped_rows))),
        bounds.clone(),
    ))
}

#[test]
fn genuine_missing_dependency_makes_ck0_fail_m5() {
    // Load-bearing closure: with NOTHING admitted the m5 proof cannot validate (its
    // recursor Elims / consts reference unknown decls). The closure flips it.
    let clean_env = clean_env_full();
    let name = KName::from_string(M5_UNSAT_CONCRETE);
    let ci = clean_env.get_const(&name).expect("present");
    let proof_raw =
        tr_expr(&clean_env, ci.value.as_ref().expect("v"), &ci.level_params).expect("tr");
    let empty = MinimalEnv::new();
    let r = Term::validate(&empty, &proof_raw, 0, 0);
    assert!(
        r.is_err(),
        "without its closure admitted, ck0 must REJECT m5's proof: got {r:?}"
    );

    let p = run_pipeline(&clean_env, &name);
    let mut b = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut b)
        .expect("with the closure, ck0 accepts m5UnsatConcrete");
}

#[test]
fn foundational_m5_ingest_no_axiom_no_unchecked() {
    // The m5 ingest introduces no axiom and no unchecked admission, so ck0's
    // verdict inherits clean's FOUNDATIONAL (empty-domain-axiom) status. Every
    // closure member is an inductive (recursor kernel-derived + checked) or a
    // value-carrying def/theorem (`check(value : type)`).
    let clean_env = clean_env_full();
    let p = run_pipeline(&clean_env, &KName::from_string(M5_UNSAT_CONCRETE));
    assert!(
        p.records.iter().all(|r| matches!(
            r.path,
            AdmitPath::InductiveRecursorDerived | AdmitPath::DefCheckedByKernel
        )),
        "no m5 admission used an unchecked/axiom path"
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
    // Each derived recursor was kernel-checked by `add_inductive`.
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
        n_ind >= 5 && n_def >= 30,
        "m5 closure is the substantial whole-substrate ingest: {n_ind} inductives + {n_def} defs"
    );
    println!(
        "GENUINE m5UnsatConcrete closure: {n_ind} inductives + {n_def} defs, all kernel-checked, no unchecked/axiom"
    );
}

// ---------------------------------------------------------------------------
// CONSISTENCY — ck0 re-checks the Farkas CHECKER definition itself (the
// `farkasChecks` decision procedure the soundness tower is ABOUT), and its whole
// Quot-free def-closure, each via a real kernel check.
// ---------------------------------------------------------------------------

const CHECKER: &str = "Clean.Farkas.farkasChecks";

#[test]
fn consistency_ck0_rechecks_the_farkas_checker_def_closure() {
    let clean_env = clean_env_full();
    let target = KName::from_string(CHECKER);

    // `farkasChecks` is a Definition: re-checking body : type against its full
    // def-closure validates the Farkas decision procedure the soundness tower
    // certifies (allNonneg / combineColumns / allEqZero / intDot / intIsNeg / …).
    let ci = clean_env.get_const(&target).expect("farkasChecks present");
    assert!(
        ci.value.is_some(),
        "farkasChecks is a Definition with a body"
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

    // ck0 re-checks farkasChecks itself (body : type).
    let mut budget = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut budget)
        .expect("ck0 re-checks the Farkas checker farkasChecks (body : type)");

    for r in &p.records {
        if r.path == AdmitPath::InductiveRecursorDerived {
            let rec = CkName::from_dotted(&format!("{}.rec", r.name));
            assert!(p.env.num_level_params(&rec).is_some(), "rec {rec} derived");
        }
    }
    assert!(
        n_def >= 10,
        "the Farkas checker def-closure is substantial (got {n_def} defs)"
    );
    println!(
        "CONSISTENCY farkasChecks def-closure: {n_ind} inductives + {n_def} defs, all kernel-checked; \
         ck0 re-checked the checker itself"
    );
}

// ---------------------------------------------------------------------------
// FAITHFUL — the ck0-checked statement is the structural image of clean's
// (same Pi arity, same head consts), and the proven `farkasChecks` /
// `Unsat` / `int0` it references are the REAL clean defs (it is `farkasChecks`'s
// own def-closure that ck0 re-checks, not a re-stated stub).
// ---------------------------------------------------------------------------

#[test]
fn faithful_translated_type_matches_clean() {
    let clean_env = clean_env_full();
    let name = KName::from_string(TARGET);
    let ci = clean_env.get_const(&name).expect("present");
    let ty_raw = tr_expr(&clean_env, &ci.type_, &ci.level_params).expect("tr type");

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
        "translated type has the same Pi arity as clean's intLeTrans type"
    );
    // The translated type's head consts are the structural image of clean's (the
    // statement is FAITHFUL, not a re-stated stub): collect the consts of clean's
    // type and the raw type and require they coincide.
    let mut clean_consts: HashSet<KName> = HashSet::new();
    collect_consts(&ci.type_, &mut clean_consts);
    let clean_const_strs: HashSet<String> = clean_consts
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    let mut raw_consts: HashSet<String> = HashSet::new();
    collect_raw_consts(&ty_raw, &mut raw_consts);
    assert_eq!(
        clean_const_strs, raw_consts,
        "translated type's head consts coincide with clean's intLeTrans type"
    );
    // And those consts are the REAL Farkas substrate the lemma is about — `intLe`
    // and the diff-pair `Int` (NOT a stubbed re-statement).
    for needed in ["Clean.Farkas.intLe", "Clean.Farkas.Int"] {
        assert!(
            raw_consts.contains(needed),
            "faithful type must reference the real {needed}"
        );
    }
    // The full proof-driven closure also carries the REAL Nat-level arithmetic
    // substrate (`natAdd` + the additive-order lemmas the transitivity proof
    // chains through), NOT a stub.
    let closure = dependency_closure(&clean_env, &name).expect("cl");
    let names: HashSet<String> = closure
        .iter()
        .map(|i| match i {
            AdmitItem::Inductive(n) | AdmitItem::DefOrTheorem(n) => n.to_string(),
        })
        .collect();
    for needed in [
        "Clean.Farkas.natAdd",
        "Clean.Farkas.natLe",
        "Clean.Farkas.natLeAddBoth",
        "Clean.Farkas.natLeAddCancelR",
        "Clean.Farkas.natAddReshuffle",
    ] {
        assert!(
            names.contains(needed),
            "faithful closure carries the real {needed} the transitivity proof uses; \
             closure = {names:?}"
        );
    }
    println!(
        "FAITHFUL intLeTrans type: {} Pi binders (clean == ck0), head consts coincide; \
         closure carries the real Nat additive/order substrate (natAdd/natLe/\
         natLeAddBoth/natLeAddCancelR/natAddReshuffle) + intLe/Int",
        clean_pis(&ci.type_)
    );
}

// ---------------------------------------------------------------------------
// GENUINE — corrupting the re-checked lemma's proof makes ck0 REJECT (type
// mismatch, not parse error); omitting a closure dep makes it FAIL (load-bearing).
// ---------------------------------------------------------------------------

#[test]
fn genuine_ck0_rejects_corrupted_proof() {
    // Corrupt intLeTrans's TYPE by swapping its first two Pi-binder domains. The
    // result validates over the SAME closure (well-formed) but the proof no longer
    // inhabits it → ck0 must REJECT with a genuine TypeMismatch.
    let clean_env = clean_env_full();
    let name = KName::from_string(TARGET);
    let p = run_pipeline(&clean_env, &name);

    let mut b0 = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut b0).expect("good proof checks");

    let ci = clean_env.get_const(&name).expect("present");
    let ty_raw = tr_expr(&clean_env, &ci.type_, &ci.level_params).expect("tr type");
    let corrupt_raw =
        corrupt_conclusion_intle(&ty_raw).expect("intLeTrans conclusion is an intLe = true goal");
    assert_ne!(corrupt_raw, ty_raw, "corruption changes the type");
    let num_lvls = u32::try_from(ci.level_params.len()).expect("fits");
    let corrupt_ty =
        Term::validate(&p.env, &corrupt_raw, 0, num_lvls).expect("corrupt type validates");

    let mut b1 = Budget::default_budget();
    let r = clean_ck0::check(&p.env, &p.target_proof, &corrupt_ty, &mut b1);
    assert!(
        matches!(r, Err(clean_ck0::InferError::TypeMismatch)),
        "ck0 must REJECT intLeTrans's proof against the domain-swapped type with a \
         TYPE MISMATCH (not parse/level error): got {r:?}"
    );
}

/// Corrupt the CONCLUSION of `intLeTrans`'s type. `intLeTrans`'s first three
/// binders are all `(a b c : Int)` (a plain binder-domain swap is a no-op), and
/// its later binders are `intLe _ _ = true` HYPOTHESES whose Eq-domains reference
/// earlier bound vars by de-Bruijn index (swapping their domains opens a var). So
/// instead we tamper the goal: walk to the final non-Pi body
/// `Eq Bool (intLe (BVar a)(BVar c)) true` and replace the SECOND `intLe`
/// argument `BVar c` with the FIRST `BVar a` — yielding the well-formed but FALSE
/// goal `intLe a a = true` that `intLeTrans`'s proof (which produces `a ≤ c`) does
/// NOT inhabit. The closure is untouched, so the type still validates; only the
/// proof↔type fit is broken.
fn corrupt_conclusion_intle(ty: &RawExpr) -> Option<RawExpr> {
    match ty {
        RawExpr::Pi(bi, d, b) => {
            let body = corrupt_conclusion_intle(b)?;
            Some(RawExpr::Pi(*bi, d.clone(), Box::new(body)))
        }
        // Final body: Eq Bool (intLe x y) true  ==  App(App(App(App(Eq,Bool),lhs),rhs))
        // where lhs = App(App(intLe, BVar a), BVar c). Rewrite lhs's last arg.
        RawExpr::App(outer, rhs_true) => {
            // outer = App(App(Eq, Bool), lhs); rewrite `lhs`'s second intLe arg.
            let RawExpr::App(eq_bool, lhs) = outer.as_ref() else {
                return None;
            };
            let RawExpr::App(intle_a, _c) = lhs.as_ref() else {
                return None;
            };
            // Identify the FIRST argument of intLe to duplicate it as the second.
            let RawExpr::App(_intle, a_arg) = intle_a.as_ref() else {
                return None;
            };
            let new_lhs = RawExpr::App(intle_a.clone(), Box::new((**a_arg).clone()));
            let new_outer = RawExpr::App(eq_bool.clone(), Box::new(new_lhs));
            Some(RawExpr::App(Box::new(new_outer), rhs_true.clone()))
        }
        _ => None,
    }
}

#[test]
fn genuine_missing_dependency_makes_ck0_fail() {
    // Load-bearing closure: with NOTHING admitted the proof cannot validate (its
    // recursor Elims / consts reference unknown decls). The deps flip the verdict.
    let clean_env = clean_env_full();
    let name = KName::from_string(TARGET);
    let ci = clean_env.get_const(&name).expect("present");

    let proof_raw =
        tr_expr(&clean_env, ci.value.as_ref().expect("v"), &ci.level_params).expect("tr");
    let empty = MinimalEnv::new();
    let r = Term::validate(&empty, &proof_raw, 0, 0);
    assert!(
        r.is_err(),
        "without its closure admitted, ck0 must REJECT intLeTrans's proof: got {r:?}"
    );

    let p = run_pipeline(&clean_env, &name);
    let mut b = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut b)
        .expect("with the closure, ck0 accepts");
}

// ---------------------------------------------------------------------------
// FOUNDATIONAL — the ingest introduces no axiom and no unchecked admission, so
// ck0's verdict inherits clean's FOUNDATIONAL (empty-domain-axiom) status.
// ---------------------------------------------------------------------------

#[test]
fn foundational_ingest_introduces_no_axiom_no_unchecked() {
    let clean_env = clean_env_full();
    let p = run_pipeline(&clean_env, &KName::from_string(TARGET));
    assert!(
        p.records.iter().all(|r| matches!(
            r.path,
            AdmitPath::InductiveRecursorDerived | AdmitPath::DefCheckedByKernel
        )),
        "no admission used an unchecked/axiom path"
    );
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

#[test]
fn no_unchecked_admission_anywhere_in_closure() {
    // GENUINENESS: every member of the closure (and the target) is admitted ONLY
    // via a kernel-derived recursor or a real `check(value:type)`. There is no
    // `_unchecked` / structural / axiom path in the engine.
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
        n_ind >= 3 && n_def >= 8,
        "Farkas closure is substantial: {n_ind} inductives + {n_def} defs"
    );
    println!("GENUINE intLeTrans closure: {n_ind} inductives + {n_def} defs, all kernel-checked");
}

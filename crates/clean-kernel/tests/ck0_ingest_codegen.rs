// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! ck2 INGEST BRIDGE — CODEGEN: `clean-ck0` INDEPENDENTLY re-checks clean's
//! PROVED gate-fidelity codegen lowering identity through the EXISTING
//! clean→ck0 bridge.
//!
//! This closes the named honest-floor item: today `clean-ck0` already re-checks
//! math / software (resolution) / AI (Farkas), but the CODEGEN re-check still
//! used `clean-kernel`'s bitvec gate-fidelity layer. Here the MINIMAL kernel
//! re-checks the codegen identity itself.
//!
//! It mirrors `ck0_ingest_farkas.rs` / `ck0_ingest_capstone.rs` EXACTLY (same
//! translator, same env-chained topological dependency-closure engine, same
//! `run_pipeline` / `ck0_rechecks` discipline — NO `_unchecked` path, every
//! inductive's recursor kernel-derived + checked, every def/theorem admitted
//! only after a real `clean_ck0::check(value : type)`), and points it at the
//! computational gate-fidelity layer registered by
//! [`clean_kernel::Environment::init_bv_compute`].
//!
//! HEADLINE (GUARANTEED proved, NON-REFLEXIVE): `Clean.BV4.bvAdd_comm :
//! (a b : Clean.BV4) -> bvEq (bvAdd a b) (bvAdd b a)` — the kernel image of the
//! REAL GVN commutative-op canonicalization (`trust_cg_opt::gvn` canonicalizes
//! `op(x,y)`/`op(y,x)` to one value number; sound iff the op commutes). Its
//! conclusion `bvEq (bvAdd a b) (bvAdd b a)` is genuinely non-reflexive: `bvAdd
//! a b` and `bvAdd b a` are STRUCTURALLY DISTINCT terms (operands swapped), so a
//! `refl` proof would NOT type-check — the genuine proof is real per-bit
//! ripple-carry Boolean reasoning (full `Bool.rec` case split over all 8 operand
//! bits, each leaf closed by ι/δ-reduction of the actual `xor3`/`maj` adder
//! gate trees). `bvAdd` is the FAITHFUL width-4 ripple-carry adder
//! (`sumᵢ = xor3(xᵢ,yᵢ,cᵢ)`, `cᵢ₊₁ = maj(xᵢ,yᵢ,cᵢ)`), so ck0 re-checking the
//! identity reduces the actual gate trees — a wrong-bit / wrong-carry encoding
//! would be REJECTED.
//!
//! `bvAdd_comm` is a real `Declaration::Theorem` with EMPTY domain-axiom
//! closure (axiom closure ⊆ FOUNDATIONAL_AXIOMS; see `bitvec_compute_tests.rs`
//! `test_bvadd_comm_is_proved_and_axiom_closure_foundational`), so ck0
//! re-checking it inherits clean's FOUNDATIONAL status. We additionally ingest
//! `Clean.BV4.bvSub_self : (a) -> bvEq (bvSub a a) bvZero` — the non-reflexive
//! self-difference identity (`bvSub a a` and `bvZero` are distinct terms).
//!
//! DISCIPLINE: `clean-ck0/src` is NOT modified; `clean-kernel/src` is untouched
//! (dev-dep test). The bridge engine is COPIED verbatim from the Farkas ingest —
//! no new bridge feature was needed (the gate-fidelity closure is Quot-free
//! Bool/And/Eq/`Clean.BV4`-structure, the SAME shape the capstone already
//! ingests). NEITHER `is_identical` / reflexivity (the bvEq goal's two sides are
//! distinct, so a refl proof does not type-check) NOR an `_unchecked` admission
//! appears anywhere.

use std::collections::HashSet;

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
                // A small-eliminating Prop inductive (Or/And/False…) has NO
                // motive universe param in clean: take Zero (Prop) as the
                // faithful motive level. Otherwise take clean's leading slot.
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
            deps.sort_by_key(KName::to_string);
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
            deps.sort_by_key(KName::to_string);
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
        "codegen closure covers single (non-mutual) inductives only"
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
        .expect("codegen closure admits only value-carrying defs/theorems (no opaque deps)");
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

/// Clean env holding the PROVED computational gate-fidelity bitvec layer (the
/// width-4 carrier `Clean.BV4`, the ripple-carry `bvAdd`/`bvSub`, the per-bit
/// `bvEq`, and the PROVED non-reflexive identities `bvAdd_comm`/`bvSub_self`/
/// `bvAdd_zero`). This is the SAME layer the criterion-2 GVN lowering bridge
/// trusts for gate fidelity.
fn clean_env_codegen() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_bv_compute()
        .expect("clean init_bv_compute (registers the PROVED gate-fidelity bitvec layer)");
    env
}

// ===========================================================================
// TESTS
// ===========================================================================

/// HEADLINE: the PROVED non-reflexive commutativity gate-fidelity identity —
/// the kernel image of the real GVN commutative-op canonicalization.
const BV_ADD_COMM: &str = "Clean.BV4.bvAdd_comm";

/// Reduction budget for the gate-fidelity re-checks.
///
/// `Budget::default_budget()` (1M steps) is sized for the corpus shapes M1
/// exercises; the width-4 `bvAdd_comm` proof is a genuinely larger reduction —
/// a 256-leaf (8-bit) nested `Bool.rec` case split where EACH leaf forces the
/// kernel to ι/δ-reduce the full ripple-carry adder gate tree (`xor3`/`maj` per
/// bit) on BOTH `bvAdd a b` and `bvAdd b a`. We raise the fuel accordingly. This
/// is SOUND and fail-closed: the budget meter only ever decrements and an
/// exhausted budget collapses to *reject* (`OutOfBudget` -> rejection in
/// `def_eq`/`check`), so a larger budget can never make an unsound term pass —
/// it only lets a genuine, terminating reduction finish. (`clean-ck0/src` is
/// UNCHANGED; `Budget::new` is the crate's public, fail-closed fuel knob.)
fn gate_budget() -> Budget {
    Budget::new(64_000_000)
}
/// The non-reflexive self-difference identity `a - a = 0`.
const BV_SUB_SELF: &str = "Clean.BV4.bvSub_self";
/// The additive-identity gate-fidelity identity `a + 0 = a`.
const BV_ADD_ZERO: &str = "Clean.BV4.bvAdd_zero";

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

    let mut budget = gate_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut budget)
        .unwrap_or_else(|e| panic!("ck0 failed to re-check {name}: {e:?}"));
    // Non-vacuous: inferred def-eq to declared.
    let mut b2 = gate_budget();
    let inferred = clean_ck0::infer(&p.env, &p.target_proof, &mut b2).expect("infer target");
    let mut b3 = gate_budget();
    assert!(
        clean_ck0::is_def_eq(&p.env, &inferred, &p.target_ty, &mut b3).expect("def_eq"),
        "{name}: inferred type def-eq to translated clean type"
    );
    p.records.len() + 1
}

// ---------------------------------------------------------------------------
// HEADLINE — ck0 INDEPENDENTLY re-checks the PROVED non-reflexive gate-fidelity
// commutativity identity `bvAdd_comm`, climbing its whole Bool/And/Eq/BV4
// closure. This is the codegen-kingdom re-check moved onto the MINIMAL kernel.
// ---------------------------------------------------------------------------

#[test]
fn codegen_ck0_rechecks_bv_add_comm() {
    // `bvAdd_comm : (a b : Clean.BV4) -> bvEq (bvAdd a b) (bvAdd b a)`. The kernel
    // image of the REAL GVN commutative-op canonicalization. Its conclusion is
    // genuinely NON-REFLEXIVE (`bvAdd a b` / `bvAdd b a` are distinct terms); the
    // proof is real per-bit ripple-carry Boolean reasoning over the FAITHFUL
    // width-4 adder (8-bit `Bool.rec` case split, each leaf closed by ι/δ of the
    // actual `xor3`/`maj` gate trees). ck0 climbs its Quot-free closure and
    // re-checks the proof — the SAME shape the capstone/Farkas bridge ingests.
    let clean_env = clean_env_codegen();
    let n = ck0_rechecks(&clean_env, BV_ADD_COMM);
    assert!(
        n > 5,
        "bvAdd_comm closure is genuinely multi-decl (BV4/Bool/And/Eq + adder defs); got {n}"
    );
    println!("CODEGEN bvAdd_comm: ck0 re-checked the gate-fidelity commutativity identity (env-chained closure {n} decls)");
}

#[test]
fn codegen_ck0_rechecks_bv_sub_self() {
    // `bvSub_self : (a : Clean.BV4) -> bvEq (bvSub a a) bvZero`. The non-reflexive
    // self-difference identity `a - a = 0`; `bvSub a a` and `bvZero` are distinct
    // terms. ck0 re-checks it through the env-chained closure.
    let clean_env = clean_env_codegen();
    let n = ck0_rechecks(&clean_env, BV_SUB_SELF);
    assert!(
        n > 5,
        "bvSub_self closure is genuinely multi-decl (got {n})"
    );
    println!("CODEGEN bvSub_self: ck0 re-checked (env-chained closure {n} decls)");
}

#[test]
fn codegen_ck0_rechecks_bv_add_zero() {
    // `bvAdd_zero : (a : Clean.BV4) -> bvEq (bvAdd a bvZero) a`. Additive-identity
    // gate fidelity; non-reflexive (`bvAdd a bvZero` vs the bare `a`).
    let clean_env = clean_env_codegen();
    let n = ck0_rechecks(&clean_env, BV_ADD_ZERO);
    assert!(
        n > 5,
        "bvAdd_zero closure is genuinely multi-decl (got {n})"
    );
    println!("CODEGEN bvAdd_zero: ck0 re-checked (env-chained closure {n} decls)");
}

// ---------------------------------------------------------------------------
// NON-REFLEXIVE / NON-VACUOUS — the two sides of the re-checked `bvEq` goal are
// STRUCTURALLY DISTINCT terms, so this is NOT the forbidden reflexivity tautology.
// ---------------------------------------------------------------------------

#[test]
fn non_reflexive_bv_add_comm_sides_are_distinct() {
    // The headline goal is `bvEq (bvAdd a b) (bvAdd b a)`. We confirm, on the
    // clean side, that `bvAdd a b` and `bvAdd b a` are NOT syntactically equal —
    // so the ck0-re-checked proof is genuine per-bit reasoning, NOT
    // reflexivity-in-disguise (a refl proof would not type-check against bvEq).
    let clean_env = clean_env_codegen();
    let name = KName::from_string(BV_ADD_COMM);
    let ci = clean_env.get_const(&name).expect("bvAdd_comm present");

    // Walk to the conclusion `bvEq (bvAdd a b) (bvAdd b a)` under the 2 Pi binders
    // and check the two `bvAdd` argument spines differ.
    let mut cur = ci.type_.clone();
    let mut pis = 0u32;
    while let ExprKind::Pi(_, _, b) = cur.kind() {
        pis += 1;
        cur = (**b).clone();
    }
    assert_eq!(pis, 2, "bvAdd_comm binds (a b : Clean.BV4)");
    // cur = App(App(bvEq, lhs), rhs); lhs = bvAdd a b, rhs = bvAdd b a.
    let ExprKind::App(bveq_lhs, rhs) = cur.kind() else {
        panic!("conclusion is a bvEq application");
    };
    let ExprKind::App(_bveq, lhs) = bveq_lhs.kind() else {
        panic!("conclusion is bvEq applied to two args");
    };
    assert_ne!(
        lhs.kind(),
        rhs.kind(),
        "bvAdd a b and bvAdd b a must be STRUCTURALLY DISTINCT (non-reflexive goal)"
    );
    println!(
        "NON-REFLEXIVE bvAdd_comm: the two bvEq sides (bvAdd a b / bvAdd b a) are distinct terms"
    );
}

// ---------------------------------------------------------------------------
// FAITHFUL — the ck0-re-checked statement is the structural image of clean's
// `bvAdd_comm` type; closure carries the REAL gate-fidelity adder substrate.
// ---------------------------------------------------------------------------

#[test]
fn faithful_bv_add_comm_type_matches_clean() {
    let clean_env = clean_env_codegen();
    let name = KName::from_string(BV_ADD_COMM);
    let ci = clean_env.get_const(&name).expect("bvAdd_comm present");
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
        "translated type has the same Pi arity (a b : Clean.BV4) as clean's"
    );
    assert_eq!(clean_pis(&ci.type_), 2, "bvAdd_comm binds a, b");

    // Head consts of the translated type coincide with clean's, and reference the
    // REAL bvEq / bvAdd / BV4 gate-fidelity substrate (NOT a stub).
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
        "translated type's head consts coincide with clean's bvAdd_comm type"
    );
    for needed in ["Clean.BV4.bvEq", "Clean.BV4.bvAdd", "Clean.BV4"] {
        assert!(
            raw_consts.contains(needed),
            "faithful type must reference the real {needed}; got {raw_consts:?}"
        );
    }

    // The full proof-driven closure carries the REAL faithful ripple-carry adder
    // gate substrate (`xor3`/`maj`) the commutativity proof reduces through.
    let closure = dependency_closure(&clean_env, &name).expect("cl");
    let names: HashSet<String> = closure
        .iter()
        .map(|i| match i {
            AdmitItem::Inductive(n) | AdmitItem::DefOrTheorem(n) => n.to_string(),
        })
        .collect();
    for needed in [
        "Clean.BV4",
        "Clean.BV4.bvAdd",
        "Clean.BV4.bvEq",
        "Clean.BV4.xor3",
        "Clean.BV4.maj",
    ] {
        assert!(
            names.contains(needed),
            "faithful bvAdd_comm closure carries the real {needed}; closure = {names:?}"
        );
    }
    println!(
        "FAITHFUL bvAdd_comm type: {} Pi binders (clean == ck0), head consts coincide; \
         closure carries the real faithful ripple-carry adder gate substrate (bvAdd/xor3/maj)",
        clean_pis(&ci.type_)
    );
}

// ---------------------------------------------------------------------------
// GENUINE — corrupting the re-checked identity's TYPE so its proof no longer
// inhabits it makes ck0 REJECT with a real TYPE MISMATCH (not a parse error).
// ---------------------------------------------------------------------------

#[test]
fn genuine_ck0_rejects_corrupted_bv_add_comm() {
    // Corrupt the CONCLUSION so the genuine proof no longer inhabits it: in the
    // final `bvEq lhs rhs`, replace `rhs` (= bvAdd b a) with `lhs` (= bvAdd a b),
    // yielding the reflexivity goal `bvEq (bvAdd a b) (bvAdd a b)`. The genuine
    // non-reflexive proof (whose RHS is the swapped `bvAdd b a`) does NOT produce
    // it. The closure is untouched (both sides are well-typed Clean.BV4), so the
    // type still validates; only the proof↔type fit breaks → TypeMismatch.
    //
    // NB: this is the inverse of the forbidden reflexivity trap — we corrupt the
    // genuine non-reflexive goal INTO the reflexive one and confirm the genuine
    // proof is NOT a proof of it (so the genuine proof truly used the swap).
    let clean_env = clean_env_codegen();
    let name = KName::from_string(BV_ADD_COMM);
    let p = run_pipeline(&clean_env, &name);

    let mut b0 = gate_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut b0)
        .expect("good bvAdd_comm proof checks");

    let ci = clean_env.get_const(&name).expect("present");
    let ty_raw = tr_expr(&clean_env, &ci.type_, &ci.level_params).expect("tr type");
    let corrupt_raw = corrupt_conclusion_rhs_to_lhs(&ty_raw)
        .expect("bvAdd_comm conclusion is a bvEq goal under 2 Pis");
    assert_ne!(corrupt_raw, ty_raw, "corruption changes the type");
    let num_lvls = u32::try_from(ci.level_params.len()).expect("fits");
    let corrupt_ty =
        Term::validate(&p.env, &corrupt_raw, 0, num_lvls).expect("corrupt bvEq type validates");

    let mut b1 = gate_budget();
    let r = clean_ck0::check(&p.env, &p.target_proof, &corrupt_ty, &mut b1);
    assert!(
        matches!(r, Err(clean_ck0::InferError::TypeMismatch)),
        "ck0 must REJECT bvAdd_comm's proof against the RHS:=LHS-collapsed bvEq \
         type with a TYPE MISMATCH (not parse/level error): got {r:?}"
    );
    println!(
        "GENUINE bvAdd_comm: ck0 REJECTS the RHS-collapsed (reflexive) bvEq type (TypeMismatch)"
    );
}

/// Corrupt the CONCLUSION of a `(x y) -> bvEq lhs rhs` goal: walk past the Pi
/// binders to the final `bvEq lhs rhs` (spine `App(App(bvEq, lhs), rhs)`) and
/// replace `rhs` with `lhs`. Well-formed over the same closure; the genuine
/// (non-reflexive) proof does not inhabit it.
fn corrupt_conclusion_rhs_to_lhs(ty: &RawExpr) -> Option<RawExpr> {
    match ty {
        RawExpr::Pi(bi, d, b) => {
            let body = corrupt_conclusion_rhs_to_lhs(b)?;
            Some(RawExpr::Pi(*bi, d.clone(), Box::new(body)))
        }
        // Final body: bvEq lhs rhs == App(App(bvEq, lhs), rhs).
        RawExpr::App(bveq_lhs, _rhs) => {
            let RawExpr::App(_bveq, lhs) = bveq_lhs.as_ref() else {
                return None;
            };
            Some(RawExpr::App(bveq_lhs.clone(), lhs.clone()))
        }
        _ => None,
    }
}

#[test]
fn genuine_missing_dependency_makes_ck0_fail_bv_add_comm() {
    // Load-bearing closure: with NOTHING admitted the bvAdd_comm proof cannot
    // validate (its recursor Elims / consts reference unknown decls). The closure
    // flips it.
    let clean_env = clean_env_codegen();
    let name = KName::from_string(BV_ADD_COMM);
    let ci = clean_env.get_const(&name).expect("present");
    let proof_raw =
        tr_expr(&clean_env, ci.value.as_ref().expect("v"), &ci.level_params).expect("tr");
    let empty = MinimalEnv::new();
    let r = Term::validate(&empty, &proof_raw, 0, 0);
    assert!(
        r.is_err(),
        "without its closure admitted, ck0 must REJECT bvAdd_comm's proof: got {r:?}"
    );

    let p = run_pipeline(&clean_env, &name);
    let mut b = gate_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut b)
        .expect("with the closure, ck0 accepts bvAdd_comm");
}

// ---------------------------------------------------------------------------
// FOUNDATIONAL — the codegen ingest introduces no axiom and no unchecked
// admission, so ck0's verdict inherits clean's FOUNDATIONAL (empty-domain-axiom)
// status. Also confirm, on the CLEAN side, that bvAdd_comm's transitive axiom
// closure is ⊆ FOUNDATIONAL_AXIOMS (zero domain axioms) — the trust_count==0
// evidence the ingest inherits.
// ---------------------------------------------------------------------------

#[test]
fn foundational_codegen_ingest_no_axiom_no_unchecked() {
    let clean_env = clean_env_codegen();

    // (a) CLEAN-side trust_count==0: bvAdd_comm's transitive axiom closure has NO
    // domain-specific axiom (⊆ FOUNDATIONAL_AXIOMS).
    let mut domain: Vec<String> = clean_env
        .axiom_deps(&KName::from_string(BV_ADD_COMM))
        .expect("bvAdd_comm registered")
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    domain.sort();
    assert!(
        domain.is_empty(),
        "bvAdd_comm must be axiom-free (trust_count==0, ⊆ FOUNDATIONAL_AXIOMS), got {domain:?}"
    );

    // (b) ck0 ingest uses only real kernel paths — no axiom / no _unchecked.
    let p = run_pipeline(&clean_env, &KName::from_string(BV_ADD_COMM));
    assert!(
        p.records.iter().all(|r| matches!(
            r.path,
            AdmitPath::InductiveRecursorDerived | AdmitPath::DefCheckedByKernel
        )),
        "no bvAdd_comm admission used an unchecked/axiom path"
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
        n_ind >= 1 && n_def >= 3,
        "bvAdd_comm closure is substantial: {n_ind} inductives + {n_def} defs"
    );
    println!(
        "FOUNDATIONAL codegen: bvAdd_comm trust_count==0 (clean), ck0 closure \
         {n_ind} inductives + {n_def} defs, all kernel-checked, no unchecked/axiom"
    );
}

// ---------------------------------------------------------------------------
// CONSISTENCY — ck0 re-checks the gate-fidelity ADDER definition itself
// (`bvAdd`, the FAITHFUL ripple-carry the commutativity identity is ABOUT) and
// its whole def-closure (xor3/maj/bit accessors), each via a real kernel check.
// ---------------------------------------------------------------------------

const ADDER: &str = "Clean.BV4.bvAdd";

#[test]
fn consistency_ck0_rechecks_the_adder_def_closure() {
    let clean_env = clean_env_codegen();
    let target = KName::from_string(ADDER);

    let ci = clean_env.get_const(&target).expect("bvAdd present");
    assert!(ci.value.is_some(), "bvAdd is a Definition with a body");

    let p = run_pipeline(&clean_env, &target);
    assert!(
        p.records.iter().all(|r| matches!(
            r.path,
            AdmitPath::InductiveRecursorDerived | AdmitPath::DefCheckedByKernel
        )),
        "every adder-closure admission is a real kernel check"
    );

    // ck0 re-checks bvAdd itself (body : type) — the faithful ripple-carry adder
    // the GVN-commutativity gate fidelity rests on.
    let mut budget = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut budget)
        .expect("ck0 re-checks the gate-fidelity adder bvAdd (body : type)");

    for r in &p.records {
        if r.path == AdmitPath::InductiveRecursorDerived {
            let rec = CkName::from_dotted(&format!("{}.rec", r.name));
            assert!(p.env.num_level_params(&rec).is_some(), "rec {rec} derived");
        }
    }
    println!(
        "CONSISTENCY bvAdd def-closure: ck0 re-checked the faithful ripple-carry adder itself"
    );
}

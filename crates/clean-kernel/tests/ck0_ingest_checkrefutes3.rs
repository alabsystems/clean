// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! ck2 INGEST BRIDGE — CAPSTONE (SUB-QUADRATIC): `clean-ck0` INDEPENDENTLY
//! re-checks clean's NEW FAST software-soundness theorem
//! `Clean.Res.checkRefutes3_sound`.
//!
//! This is the analogue of `ck0_ingest_capstone.rs` (which re-checks the OLD
//! quadratic `Clean.Res.checkRefutes_sound`), pointed at the SUB-QUADRATIC
//! `Nat`-indexed-trie checker's soundness theorem:
//!
//!   `(cs : List (List Nat)) → (pf : List Step) →
//!      checkRefutes3 (initialTrie cs) (listLen cs) pf = true → Unsat cs`
//!
//! Its dependency closure ADDS, over `checkRefutes_sound`'s closure:
//!   * the `Clean.Res.Trie` INDUCTIVE (`leaf | node val lo hi`) + its kernel-
//!     derived recursor `Trie.rec` — a NEW inductive surface for ck0;
//!   * `trieGet` (a `Trie.rec` descent threading native `Nat.div`/`Nat.mod`/
//!     `Nat.ble` on the BigNat key per level);
//!   * `trieIns` / `trieInsAux` (a fuel `Nat.rec` descent that REBUILDS the trie);
//!   * `checkStep3`, `initialTrie` / `initialTrieGo`, `listLen`;
//!   * the soundness lemmas `trieGetSat` / `trieInsPreservesAllSat` /
//!     `checkStep3Sat` / `go3Sound` / `initialTrieAllSat`, on top of the reused
//!     `resolve_step_sat` / `mem,subset,seteq_sat` / `semantics` layer.
//!
//! THE NEW ck0 surfaces this exercises: admitting the `Trie` inductive + deriving
//! its recursor; reducing `trieGet`'s `Trie.rec` over native-`Nat` key arithmetic;
//! the fuel `Nat.rec` in `trieIns`; and the `Eq.subst` stuck-scrutinee transports
//! in the trie soundness lemmas.
//!
//! The bridge ENGINE is COPIED VERBATIM from `ck0_ingest_capstone.rs` (same
//! Elim-lowering translator, same env-chained topological dependency-closure, same
//! `run_pipeline` / `ck0_rechecks` discipline, same `Budget::default_budget()`).
//! The ONE engine ADDITION the sub-quadratic checker forces is a TRANSLATOR
//! surface the old quadratic corpus never carried: `ExprKind::Lit` — the fast
//! checker uses BigNat `Nat` LITERALS for trie keys / bit ops (`key/2`, `key%2`,
//! `Nat.ble`), so `tr_expr` now translates `Literal::Nat`/`Literal::String` to
//! `RawExpr::Lit` (ck0 reduces Nat literals natively). This is an UNTRUSTED
//! translator extension; no `clean-ck0/src` (TCB) change was needed.
//!
//! DISCIPLINE: `clean-ck0/src` is NOT modified for this test alone; `clean-kernel/
//! src` is untouched (dev-dep test). The translator is total-or-explicit-
//! `BridgeError`; every admission goes through a real kernel check (a kernel-
//! derived recursor or a real `clean_ck0::check(value : type)`); NO `_unchecked` /
//! `add_decl_structural` / axiom admission appears anywhere. A faithfulness gap is
//! a reported bug, never a silent pass.

use std::collections::HashSet;

use clean_ck0::rawexpr::{BinderInfo as CkBinderInfo, RawLevel, RawLit};
use clean_ck0::{
    add_inductive, BigNat as CkBigNat, Budget, Constructor as CkCtor, Env as CkEnv,
    InductiveDecl as CkIndDecl, MinimalEnv, Name as CkName, RawExpr, Term, Transparency,
};
use clean_kernel::{
    BigNat as KBigNat, Environment, Expr, ExprKind, Level as KLevel, Name as KName,
};

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

/// Faithfully translate a clean `BigNat` (little-endian `u64` limbs) into a ck0
/// `BigNat`, using only ck0's public arithmetic so the VALUE is preserved exactly
/// across arbitrary precision: `value = Σ limbs[i] · (2^64)^i` by Horner.
fn tr_bignat(n: &KBigNat) -> CkBigNat {
    // 2^64 as a ck0 BigNat = (2^32) · (2^32); 2^32 fits in u64.
    let two_pow_32 = CkBigNat::from_u64(1u64 << 32);
    let two_pow_64 = two_pow_32.mul(&two_pow_32);
    let mut acc = CkBigNat::zero();
    // limbs are little-endian (lowest limb first), so fold from the HIGH limb down.
    for &limb in n.limbs().iter().rev() {
        acc = acc.mul(&two_pow_64).add(&CkBigNat::from_u64(limb));
    }
    acc
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
        // Nat / String literals. The fast checker (`trieGet`/`trieInsAux`/the
        // literal-id `encode_clause` substrate) uses BigNat `Nat` LITERALS for keys
        // and bit ops (`key/2`, `key%2`, `Nat.ble`), which ck0 reduces natively.
        // The OLD `checkRefutes` corpus never carried `Lit` nodes; this is the only
        // new TRANSLATOR surface the sub-quadratic checker needs.
        ExprKind::Lit(clean_kernel::Literal::Nat(n)) => Ok(RawExpr::Lit(RawLit::Nat(tr_bignat(n)))),
        ExprKind::Lit(clean_kernel::Literal::String(s)) => {
            Ok(RawExpr::Lit(RawLit::Str(s.to_string())))
        }
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
//
// THE UNLOCK (carried over from the capstone): every closure decl is validated/
// admitted against the GROWING `ck_env` (which already holds the earlier closure
// members), not a fresh boot.
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
/// (e.g. `List`, `Nat` inside `Trie.node`) resolve.
fn admit_inductive(clean_env: &Environment, ck_env: &mut MinimalEnv, name: &KName) -> CkName {
    let decl = clean_env
        .inductive_decl_of(name)
        .expect("inductive present (closure guarantees it)");
    assert_eq!(
        decl.types.len(),
        1,
        "checkRefutes3 closure covers single (non-mutual) inductives only"
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
        .expect("checkRefutes3 admits only value-carrying defs/theorems (no opaque deps)");
    let val_raw = tr_expr(clean_env, value, lps).expect("translate dep value");
    let val = Term::validate(ck_env, &val_raw, 0, num_lvls).expect("dep value validates");

    // REAL check: ck0 must accept value : type before admission.
    let mut budget = recheck_budget();
    if let Err(e) = clean_ck0::check(ck_env, &val, &ty, &mut budget) {
        let mut b2 = recheck_budget();
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
        .expect("clean init_resolution_soundness (admits the whole checkRefutes3_sound corpus)");
    env
}

/// Reduction budget for the sub-quadratic-checker re-checks.
///
/// VERIFIED: the DEFAULT 1M-step budget already suffices for the entire
/// `checkRefutes3_sound` closure — including the new `Trie.rec` descent
/// (`trieGet`, threading native `Nat.div`/`Nat.mod`/`Nat.ble` per level) and the
/// fuel `Nat.rec` trie rebuild (`trieIns`/`trieInsAux`). Those reductions are
/// SYMBOLIC (the trie soundness lemmas reason over a VARIABLE db/key, so no
/// concrete trie is built or descended), so the trie surfaces do NOT inflate the
/// fuel the way the codegen `bvAdd_comm` 256-leaf ground reduction does. We
/// therefore mirror the original capstone's `Budget::default_budget()` exactly —
/// no gratuitous fuel raise.
///
/// (Were a larger budget ever needed it would remain SOUND and fail-closed: the
/// meter only DECREMENTS and an exhausted budget collapses to *reject*
/// — `OutOfBudget` -> rejection in `def_eq`/`check` — so more fuel can never make
/// an unsound term pass, only let a genuine terminating reduction finish.)
fn recheck_budget() -> Budget {
    Budget::default_budget()
}

// ===========================================================================
// TESTS
// ===========================================================================

/// THE TARGET: the sub-quadratic trie checker's soundness theorem.
const TARGET: &str = "Clean.Res.checkRefutes3_sound";
/// The fast checker the soundness theorem is ABOUT (consistency: ck0 re-checks the
/// same `Definition` whose soundness it certifies).
const CHECKER: &str = "Clean.Res.checkRefutes3";

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

    let mut budget = recheck_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut budget)
        .unwrap_or_else(|e| panic!("ck0 failed to re-check {name}: {e:?}"));
    // Non-vacuous: inferred def-eq to declared.
    let mut b2 = recheck_budget();
    let inferred = clean_ck0::infer(&p.env, &p.target_proof, &mut b2).expect("infer target");
    let mut b3 = recheck_budget();
    assert!(
        clean_ck0::is_def_eq(&p.env, &inferred, &p.target_ty, &mut b3).expect("def_eq"),
        "{name}: inferred type def-eq to translated clean type"
    );
    p.records.len() + 1
}

// ---------------------------------------------------------------------------
// NEW-SURFACE WARM-UPS — the `Trie` inductive + its `Trie.rec` descent
// (`trieGet`) + the fuel `Nat.rec` rebuild (`trieIns`), each re-checked by ck0.
// These are the surfaces the OLD capstone never touched.
// ---------------------------------------------------------------------------

#[test]
fn surface_ck0_admits_trie_inductive_and_derives_recursor() {
    // The `Clean.Res.Trie` inductive (`leaf | node val lo hi`) is the NEW inductive
    // surface. ck0 must admit it via `add_inductive` (kernel-DERIVING + checking
    // `Trie.rec` + its ι-rules), not a structural/unchecked path.
    let clean_env = clean_env_full();
    let trie = KName::from_string("Clean.Res.Trie");
    let closure = dependency_closure(&clean_env, &trie).expect("Trie closure");
    let admitted = admit_closure_except_target(&clean_env, &closure, &KName::from_string("__none"));

    // Trie itself is in the closure (it is the target's own inductive).
    let rec = CkName::from_dotted("Clean.Res.Trie.rec");
    assert!(
        admitted.env.num_level_params(&rec).is_some(),
        "ck0 kernel-derived the Trie.rec recursor"
    );
    assert!(
        admitted
            .records
            .iter()
            .any(|r| r.name == CkName::from_dotted("Clean.Res.Trie")
                && r.path == AdmitPath::InductiveRecursorDerived),
        "Trie admitted via the kernel-derived-recursor path"
    );
    println!("SURFACE Trie: ck0 admitted the inductive + derived Trie.rec");
}

#[test]
fn surface_ck0_rechecks_trie_get() {
    // `trieGet : Trie → Nat → List Nat` is the `Trie.rec` descent threading native
    // `Nat.div`/`Nat.mod`/`Nat.ble` on the BigNat key per level. ck0 re-checks its
    // body : type — exercising Trie.rec reduction over native Nat key arithmetic.
    let clean_env = clean_env_full();
    let n = ck0_rechecks(&clean_env, "Clean.Res.trieGet");
    assert!(
        n > 3,
        "trieGet closure is multi-decl (Trie/Nat/Bool/List); got {n}"
    );
    println!("SURFACE trieGet: ck0 re-checked the Trie.rec descent (closure {n} decls)");
}

#[test]
fn surface_ck0_rechecks_trie_ins() {
    // `trieIns` / `trieInsAux` is the fuel `Nat.rec` descent that REBUILDS the
    // trie. ck0 re-checks it — exercising the fuel-Nat.rec surface.
    let clean_env = clean_env_full();
    let n = ck0_rechecks(&clean_env, "Clean.Res.trieIns");
    assert!(n > 3, "trieIns closure is multi-decl; got {n}");
    println!("SURFACE trieIns: ck0 re-checked the fuel-Nat.rec trie rebuild (closure {n} decls)");
}

// ---------------------------------------------------------------------------
// CONSISTENCY — ck0 re-checks the FAST CHECKER the soundness theorem is about,
// and its WHOLE def-closure, each via a real kernel check.
// ---------------------------------------------------------------------------

#[test]
fn consistency_ck0_rechecks_the_whole_checker3_def_closure() {
    let clean_env = clean_env_full();
    let target = KName::from_string(CHECKER);

    // `checkRefutes3` is a Definition: re-checking body : type against its full
    // def-closure validates the ENTIRE fast checker the soundness theorem certifies.
    let ci = clean_env.get_const(&target).expect("checkRefutes3 present");
    assert!(
        ci.value.is_some(),
        "checkRefutes3 is a Definition with a body"
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
        "every checker3-closure admission is a real kernel check"
    );

    // ck0 re-checks checkRefutes3 itself (body : type).
    let mut budget = recheck_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut budget)
        .expect("ck0 re-checks the fast checker checkRefutes3 (body : type)");

    // The whole checker def-closure is present + every recursor kernel-derived,
    // including the NEW Trie.rec.
    for r in &p.records {
        if r.path == AdmitPath::InductiveRecursorDerived {
            let rec = CkName::from_dotted(&format!("{}.rec", r.name));
            assert!(p.env.num_level_params(&rec).is_some(), "rec {rec} derived");
        }
    }
    // The Trie inductive specifically is present (the NEW surface vs the old checker).
    assert!(
        p.records
            .iter()
            .any(|r| r.name == CkName::from_dotted("Clean.Res.Trie")),
        "checkRefutes3 closure includes the NEW Trie inductive"
    );
    assert!(
        n_def >= 15,
        "the fast-checker def-closure is substantial (got {n_def} defs)"
    );
    println!(
        "CONSISTENCY checkRefutes3 def-closure: {n_ind} inductives + {n_def} defs, all \
         kernel-checked; ck0 re-checked the fast checker itself"
    );
}

// ---------------------------------------------------------------------------
// THE CAPSTONE — REACHED. clean-ck0 INDEPENDENTLY re-checks the NEW
// sub-quadratic software-kingdom soundness bridge `Clean.Res.checkRefutes3_sound`.
// ---------------------------------------------------------------------------

#[test]
fn capstone_ck0_rechecks_check_refutes3_sound() {
    // THE CAPSTONE (sub-quadratic). The full dependency closure of
    // `checkRefutes3_sound` — which ADDS the `Trie` inductive + `Trie.rec` descent
    // (`trieGet`), the fuel-`Nat.rec` rebuild (`trieIns`), and the trie soundness
    // lemmas — is admitted into a fresh ck0 env (EVERY inductive's recursor kernel-
    // derived + checked; EVERY def/theorem admitted only after a real
    // `clean_ck0::check(value : type)`), then ck0 INDEPENDENTLY decides that the
    // proof value checks against the translated type. `ck0_rechecks` asserts:
    //   * every admission took a real kernel path (no unchecked/structural/axiom);
    //   * every derived recursor exists (kernel-checked type + ι-rules);
    //   * ck0 `check(proof : type)` PASSES; and
    //   * the verdict is non-vacuous (inferred type def-eq to the translated type).
    // This extends the proved software-kingdom bridge to the FAST checker.
    let clean_env = clean_env_full();
    let n = ck0_rechecks(&clean_env, TARGET);
    assert!(
        n > 20,
        "checkRefutes3_sound closure is the full multi-inductive/multi-def bridge (got {n})"
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
    // The NEW Trie inductive is in the closure and its recursor is kernel-derived.
    assert!(
        p.records
            .iter()
            .any(|r| r.name == CkName::from_dotted("Clean.Res.Trie")
                && r.path == AdmitPath::InductiveRecursorDerived),
        "Trie inductive admitted via the kernel-derived-recursor path"
    );
    assert!(
        n_ind >= 4 && n_def >= 15,
        "capstone3 closure is substantial: {n_ind} inductives + {n_def} defs"
    );
}

#[test]
fn capstone_corrupt_proof_is_rejected() {
    // GENUINENESS (negative): corrupting `checkRefutes3_sound`'s TYPE so the proof
    // no longer inhabits it makes ck0 REJECT with a real TYPE MISMATCH — the
    // re-check is load-bearing, not a rubber stamp. We swap the first two Pi-binder
    // domains of the (translated) target type; it still validates (well-formed)
    // but the proof no longer checks against it.
    let clean_env = clean_env_full();
    let name = KName::from_string(TARGET);
    let p = run_pipeline(&clean_env, &name);

    // baseline: the good proof checks against the good type.
    let mut b0 = recheck_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut b0)
        .expect("good capstone3 proof checks");

    let ci = clean_env.get_const(&name).expect("present");
    let ty_raw = tr_expr(&clean_env, &ci.type_, &ci.level_params).expect("tr type");
    let corrupt_raw = swap_first_two_pi_domains_raw(&ty_raw)
        .expect("checkRefutes3_sound type has >= 2 Pi binders");
    assert_ne!(corrupt_raw, ty_raw, "corruption changes the type");
    let num_lvls = u32::try_from(ci.level_params.len()).expect("fits");
    let corrupt_ty =
        Term::validate(&p.env, &corrupt_raw, 0, num_lvls).expect("corrupt type validates");

    let mut b1 = recheck_budget();
    let r = clean_ck0::check(&p.env, &p.target_proof, &corrupt_ty, &mut b1);
    assert!(
        matches!(r, Err(clean_ck0::InferError::TypeMismatch)),
        "ck0 must REJECT the capstone3 proof against the domain-swapped type with a \
         TYPE MISMATCH (not a parse/level error): got {r:?}"
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
    // Load-bearing closure: with NOTHING admitted the checkRefutes3_sound proof
    // cannot validate (its recursor Elims / consts reference unknown decls). The
    // closure is what flips the verdict.
    let clean_env = clean_env_full();
    let name = KName::from_string(TARGET);
    let ci = clean_env.get_const(&name).expect("present");

    let proof_raw =
        tr_expr(&clean_env, ci.value.as_ref().expect("v"), &ci.level_params).expect("tr");
    // Empty env: nothing admitted.
    let empty = MinimalEnv::new();
    let r = Term::validate(&empty, &proof_raw, 0, 0);
    assert!(
        r.is_err(),
        "without its closure admitted, ck0 must REJECT checkRefutes3_sound's proof: got {r:?}"
    );

    // With the full closure, it passes — the deps are load-bearing.
    let p = run_pipeline(&clean_env, &name);
    let mut b = recheck_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut b)
        .expect("with the closure, ck0 accepts");
}

// ---------------------------------------------------------------------------
// FOUNDATIONAL — the ingest introduces no axiom and no unchecked admission, so
// ck0's verdict inherits clean's FOUNDATIONAL (empty-domain-axiom) status. Also
// confirm, on the CLEAN side, that checkRefutes3_sound's transitive axiom closure
// is ⊆ FOUNDATIONAL_AXIOMS (zero domain axioms) — the trust_count==0 evidence the
// ingest inherits.
// ---------------------------------------------------------------------------

#[test]
fn foundational_ingest_no_axiom_no_unchecked() {
    let clean_env = clean_env_full();

    // (a) CLEAN-side trust_count==0: checkRefutes3_sound's transitive axiom closure
    // has NO domain-specific axiom (⊆ FOUNDATIONAL_AXIOMS).
    let mut domain: Vec<String> = clean_env
        .axiom_deps(&KName::from_string(TARGET))
        .expect("checkRefutes3_sound registered")
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    domain.sort();
    assert!(
        domain.is_empty(),
        "checkRefutes3_sound must be axiom-free (trust_count==0, ⊆ FOUNDATIONAL_AXIOMS), got {domain:?}"
    );

    // (b) ck0 ingest uses only real kernel paths — no axiom / no _unchecked.
    let p = run_pipeline(&clean_env, &KName::from_string(TARGET));
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
    println!(
        "FOUNDATIONAL checkRefutes3_sound: trust_count==0 (clean axiom_deps empty), \
         ck0 ingest all real kernel paths (no unchecked/axiom)"
    );
}

// ---------------------------------------------------------------------------
// FAITHFUL — the ck0-checked statement matches clean's; the proof is non-trivial.
// ---------------------------------------------------------------------------

#[test]
fn faithful_translated_type_matches_clean() {
    // The translated type ck0 checks against is the structural image of clean's
    // theorem type (same Pi arity).
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
        "translated type has the same Pi arity as clean's checkRefutes3_sound type"
    );
    // The conclusion is `Unsat cs`, spelled δ-unfolded EXACTLY as in
    // `checkRefutes_sound`: `(H) → resConsistent H → resExclusive H →
    // allSat H cs → False`. We confirm the translated type references that SAME
    // software-soundness conclusion substrate (the bridge is genuinely about
    // refutation soundness, not a weaker statement), plus the fast checker
    // `checkRefutes3` / `initialTrie` / `listLen` in the hypothesis.
    let mut consts: HashSet<KName> = HashSet::new();
    collect_consts(&ci.type_, &mut consts);
    let strs: HashSet<String> = consts
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    for needed in [
        "Clean.Res.resConsistent",
        "Clean.Res.resExclusive",
        "Clean.Res.allSat",
        "Clean.Res.checkRefutes3",
        "Clean.Res.initialTrie",
        "Clean.Res.listLen",
        "False",
    ] {
        assert!(
            strs.contains(needed),
            "checkRefutes3_sound type must reference {needed} (same Unsat conclusion + fast \
             checker hypothesis); got {strs:?}"
        );
    }
    println!(
        "FAITHFUL checkRefutes3_sound type: {} Pi binders (clean == ck0), concludes the same \
         δ-unfolded Unsat (resConsistent/resExclusive/allSat→False) over the fast checker",
        clean_pis(&ci.type_)
    );
}

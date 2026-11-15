// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The reduction-bound theorem family (`proofs/reduction_bound.lean`), checked
//! by Clean's elaborator and kernel, with an axiom audit of every declaration.
//!
//! What `reduction_bound_all_lengths` establishes, when it passes:
//!
//! - every declaration of the file elaborates and is admitted by the kernel;
//! - the headline theorems exist with EXACTLY the statements pinned below
//!   (a pin is a second theorem whose stated type is written out here and whose
//!   proof is the headline constant, so an added hypothesis, a weakened
//!   conclusion or a changed constant fails the pin);
//! - the transitive dependency closure of every theorem in the file reaches no
//!   axiom other than the kernel's canonical foundations (propext, Quot.sound,
//!   Classical.choice), no trust marker (`sorryAx`, `trustedAy`, ...), and no
//!   opaque constant (a native-fold placeholder would be one);
//! - the audit itself is live: an axiom-backed theorem and a `sorry`-backed
//!   theorem, elaborated the same way, are both caught.
//!
//! The bound, for every length, permutation and bracketing, with `u = 1/W`:
//! `(W - h) |fl - exact| <= h * sum|x_i| + W * H` (that is
//! `|fl - exact| <= gamma_h sum|x_i| + (1 + gamma_h) H`), see the file header.

use std::collections::{BTreeSet, HashSet};

use clean_elab::tactic::builtins::builtin_tactic_patterns;
use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::expr::UsedConstants;
use clean_kernel::{ConstantKind, Name};
use clean_parser::parse_file_with_tactics_diagnostics;

const SOURCE: &str = include_str!("../../../proofs/reduction_bound.lean");

/// Statement pins for the headline theorems. Each restates the theorem's type
/// in full; the proof is the headline constant itself.
const PINS: &str = r#"
namespace ReductionBoundPins

theorem pin_sum_binary32 : ∀ (r : ReductionBound.Rounding) (u : ReductionBound.Underflow) (ct : Bool)
    (xs : List ReductionBound.Z) (t : ReductionBound.Sched), t.IsSum → List.Perm t.leaves xs →
    (∀ x : ReductionBound.Z, x ∈ xs → ReductionBound.binary32.IsFloat x) → ∀ (c : ReductionBound.Z),
    ReductionBound.eval (ReductionBound.Device.model ⟨ReductionBound.binary32, r, u, ct⟩) t = some c →
    ∀ (hb : Nat), t.height ≤ hb → hb < (ReductionBound.Device.mk ReductionBound.binary32 r u ct).W →
    ((ReductionBound.Device.mk ReductionBound.binary32 r u ct).W - hb) * ReductionBound.Z.dist c (ReductionBound.zsum xs) ≤
      hb * ReductionBound.magSum xs + (ReductionBound.Device.mk ReductionBound.binary32 r u ct).W *
        (xs.length * (ReductionBound.Device.mk ReductionBound.binary32 r u ct).etaR +
          (xs.length - 1) * (ReductionBound.Device.mk ReductionBound.binary32 r u ct).etaA) :=
  ReductionBound.reduction_bound_sum_binary32

theorem pin_sum_binary64 : ∀ (r : ReductionBound.Rounding) (u : ReductionBound.Underflow) (ct : Bool)
    (xs : List ReductionBound.Z) (t : ReductionBound.Sched), t.IsSum → List.Perm t.leaves xs →
    (∀ x : ReductionBound.Z, x ∈ xs → ReductionBound.binary64.IsFloat x) → ∀ (c : ReductionBound.Z),
    ReductionBound.eval (ReductionBound.Device.model ⟨ReductionBound.binary64, r, u, ct⟩) t = some c →
    ∀ (hb : Nat), t.height ≤ hb → hb < (ReductionBound.Device.mk ReductionBound.binary64 r u ct).W →
    ((ReductionBound.Device.mk ReductionBound.binary64 r u ct).W - hb) * ReductionBound.Z.dist c (ReductionBound.zsum xs) ≤
      hb * ReductionBound.magSum xs + (ReductionBound.Device.mk ReductionBound.binary64 r u ct).W *
        (xs.length * (ReductionBound.Device.mk ReductionBound.binary64 r u ct).etaR +
          (xs.length - 1) * (ReductionBound.Device.mk ReductionBound.binary64 r u ct).etaA) :=
  ReductionBound.reduction_bound_sum_binary64

theorem pin_dot_binary32 : ∀ (r : ReductionBound.Rounding) (u : ReductionBound.Underflow) (ct : Bool)
    (ps : List (ReductionBound.Z × ReductionBound.Z)) (t : ReductionBound.Sched), t.IsDot →
    List.Perm t.pairs ps →
    (∀ q : ReductionBound.Z × ReductionBound.Z, q ∈ ps →
      (ReductionBound.Device.mk ReductionBound.binary32 r u ct).rdQ q.1 = q.1 ∧
        (ReductionBound.Device.mk ReductionBound.binary32 r u ct).rdQ q.2 = q.2) → ∀ (c : ReductionBound.Z),
    ReductionBound.eval (ReductionBound.Device.model ⟨ReductionBound.binary32, r, u, ct⟩) t = some c →
    ∀ (hb : Nat), t.height ≤ hb → hb + 1 < (ReductionBound.Device.mk ReductionBound.binary32 r u ct).W →
    ((ReductionBound.Device.mk ReductionBound.binary32 r u ct).W - (hb + 1)) * ReductionBound.Z.dist c (ReductionBound.dotZ ps) ≤
      (hb + 1) * ReductionBound.dotAbs ps + (ReductionBound.Device.mk ReductionBound.binary32 r u ct).W *
        (ps.length * (ReductionBound.Device.mk ReductionBound.binary32 r u ct).etaG +
          (ps.length - 1) * (ReductionBound.Device.mk ReductionBound.binary32 r u ct).etaA) :=
  ReductionBound.reduction_bound_dot_binary32

theorem pin_dot_binary64 : ∀ (r : ReductionBound.Rounding) (u : ReductionBound.Underflow) (ct : Bool)
    (ps : List (ReductionBound.Z × ReductionBound.Z)) (t : ReductionBound.Sched), t.IsDot →
    List.Perm t.pairs ps →
    (∀ q : ReductionBound.Z × ReductionBound.Z, q ∈ ps →
      (ReductionBound.Device.mk ReductionBound.binary64 r u ct).rdQ q.1 = q.1 ∧
        (ReductionBound.Device.mk ReductionBound.binary64 r u ct).rdQ q.2 = q.2) → ∀ (c : ReductionBound.Z),
    ReductionBound.eval (ReductionBound.Device.model ⟨ReductionBound.binary64, r, u, ct⟩) t = some c →
    ∀ (hb : Nat), t.height ≤ hb → hb + 1 < (ReductionBound.Device.mk ReductionBound.binary64 r u ct).W →
    ((ReductionBound.Device.mk ReductionBound.binary64 r u ct).W - (hb + 1)) * ReductionBound.Z.dist c (ReductionBound.dotZ ps) ≤
      (hb + 1) * ReductionBound.dotAbs ps + (ReductionBound.Device.mk ReductionBound.binary64 r u ct).W *
        (ps.length * (ReductionBound.Device.mk ReductionBound.binary64 r u ct).etaG +
          (ps.length - 1) * (ReductionBound.Device.mk ReductionBound.binary64 r u ct).etaA) :=
  ReductionBound.reduction_bound_dot_binary64

-- The device constants, as the report states them.
theorem pin_W_rne32 (u : ReductionBound.Underflow) (ct : Bool) :
    (ReductionBound.Device.mk ReductionBound.binary32 .nearestEven u ct).W = 2 ^ 24 := rfl
theorem pin_W_rtz32 (u : ReductionBound.Underflow) (ct : Bool) :
    (ReductionBound.Device.mk ReductionBound.binary32 .towardZero u ct).W = 2 ^ 23 := rfl
theorem pin_W_rne64 (u : ReductionBound.Underflow) (ct : Bool) :
    (ReductionBound.Device.mk ReductionBound.binary64 .nearestEven u ct).W = 2 ^ 53 := rfl
theorem pin_W_rtz64 (u : ReductionBound.Underflow) (ct : Bool) :
    (ReductionBound.Device.mk ReductionBound.binary64 .towardZero u ct).W = 2 ^ 52 := rfl
theorem pin_eta_gradual_sum (f : ReductionBound.Format) (r : ReductionBound.Rounding) (ct : Bool) :
    (ReductionBound.Device.mk f r .gradual ct).etaA = 0 ∧
      (ReductionBound.Device.mk f r .gradual ct).etaR = 0 := ⟨rfl, rfl⟩
theorem pin_etaG_rne_gradual (f : ReductionBound.Format) (ct : Bool) :
    (ReductionBound.Device.mk f .nearestEven .gradual ct).etaG = 2 ^ (f.K - 1) := rfl
theorem pin_etaG_rtz_gradual (f : ReductionBound.Format) (ct : Bool) :
    (ReductionBound.Device.mk f .towardZero .gradual ct).etaG = 2 ^ f.K := rfl
theorem pin_eta_flush (f : ReductionBound.Format) (r : ReductionBound.Rounding) (ct : Bool) :
    (ReductionBound.Device.mk f r .flush ct).etaG = f.nmin ∧
      (ReductionBound.Device.mk f r .flush ct).etaA = f.nmin ∧
      (ReductionBound.Device.mk f r .flush ct).etaR = f.nmin := ⟨rfl, rfl, rfl⟩
theorem pin_binary32 : ReductionBound.binary32.K = 149 ∧ ReductionBound.binary32.t = 23 := ⟨rfl, rfl⟩
theorem pin_binary64 : ReductionBound.binary64.K = 1074 ∧ ReductionBound.binary64.t = 52 := ⟨rfl, rfl⟩

end ReductionBoundPins
"#;

/// Headline theorems whose pins must elaborate.
const HEADLINES: [&str; 4] = [
    "ReductionBound.reduction_bound_sum_binary32",
    "ReductionBound.reduction_bound_sum_binary64",
    "ReductionBound.reduction_bound_dot_binary32",
    "ReductionBound.reduction_bound_dot_binary64",
];

/// The other load-bearing statements; they must exist and pass the audit.
const CORE: [&str; 9] = [
    "ReductionBound.sched_bound",
    "ReductionBound.sum_bound",
    "ReductionBound.sum_bound_n",
    "ReductionBound.dot_bound",
    "ReductionBound.dot_bound_n",
    "ReductionBound.device_sum_bound",
    "ReductionBound.device_dot_bound",
    "ReductionBound.Device.rel_or_abs",
    "ReductionBound.leftTree_attains",
];

/// Parse (with the builtin tactic patterns, as `clean check` does), preprocess and
/// elaborate `source` into `env`. A parser recovery event, an elaboration error and
/// every failed leaf are errors.
fn elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let report = parse_file_with_tactics_diagnostics(source, &builtin_tactic_patterns())
        .map_err(|e| format!("parse error: {e:?}"))?;
    let mut failures: Vec<String> = report
        .diagnostics
        .iter()
        .map(|d| format!("parser recovery: {d:?}"))
        .collect();
    for decl in &report.decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register(env, &processed) {
            Ok(result) => collect_failures(&result, &mut failures),
            Err(e) => failures.push(format!("elaborate/kernel-check error: {e}")),
        }
    }
    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures.join("\n"))
    }
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

/// Everything a theorem's kernel check can consult, transitively.
fn closure(env: &Environment, root: &Name) -> HashSet<Name> {
    let mut seen: HashSet<Name> = HashSet::new();
    let mut stack = vec![root.clone()];
    while let Some(n) = stack.pop() {
        if !seen.insert(n.clone()) {
            continue;
        }
        if let Some(info) = env.get_const(&n) {
            let mut refs = HashSet::new();
            info.type_
                .used_constants_dag(UsedConstants::WithProjectionStructures, &mut refs);
            if let Some(v) = &info.value {
                v.used_constants_dag(UsedConstants::WithProjectionStructures, &mut refs);
            }
            stack.extend(refs.into_iter().filter(|r| !seen.contains(r)));
        }
    }
    seen
}

/// The audit verdict for one theorem: the foundational axioms it reaches, or
/// the list of everything it must not reach.
fn audit(env: &Environment, name: &Name) -> Result<BTreeSet<String>, Vec<String>> {
    let mut bad = Vec::new();
    match env.axiom_deps(name) {
        None => bad.push(format!("{name}: not registered")),
        Some(deps) if !deps.is_empty() => {
            let mut d: Vec<String> = deps.iter().map(ToString::to_string).collect();
            d.sort();
            bad.push(format!(
                "{name}: non-foundational axioms / trust markers {d:?}"
            ));
        }
        Some(_) => {}
    }
    let mut foundational = BTreeSet::new();
    for dep in closure(env, name) {
        let Some(info) = env.get_const(&dep) else {
            continue;
        };
        match info.kind {
            ConstantKind::Opaque => bad.push(format!("{name}: reaches opaque constant {dep}")),
            ConstantKind::Axiom => {
                if env.is_canonical_foundational_axiom(&dep) {
                    foundational.insert(dep.to_string());
                } else {
                    bad.push(format!("{name}: reaches axiom {dep}"));
                }
            }
            ConstantKind::Definition | ConstantKind::Theorem => {}
        }
    }
    if bad.is_empty() {
        Ok(foundational)
    } else {
        Err(bad)
    }
}

fn file_theorems(env: &Environment, prefix: &str) -> Vec<Name> {
    let mut v: Vec<Name> = env
        .constants()
        .filter(|c| c.kind == ConstantKind::Theorem && c.name.to_string().starts_with(prefix))
        .map(|c| c.name.clone())
        .collect();
    v.sort_by_key(ToString::to_string);
    v
}

#[test]
fn reduction_bound_all_lengths() {
    let mut env = Environment::with_prelude();
    if let Err(e) = elaborate_into(&mut env, SOURCE) {
        panic!("proofs/reduction_bound.lean must elaborate and kernel-check:\n{e}");
    }
    if let Err(e) = elaborate_into(&mut env, PINS) {
        panic!("a headline statement no longer matches its pin:\n{e}");
    }
    for h in HEADLINES.iter().chain(CORE.iter()) {
        assert!(
            env.get_const(&Name::from_string(h)).is_some(),
            "{h} must be registered"
        );
    }

    // No declaration of the file may be an axiom or an opaque constant.
    let foreign: Vec<String> = env
        .constants()
        .filter(|c| c.name.to_string().starts_with("ReductionBound"))
        .filter(|c| matches!(c.kind, ConstantKind::Axiom | ConstantKind::Opaque))
        .map(|c| c.name.to_string())
        .collect();
    assert!(
        foreign.is_empty(),
        "the file declares axioms/opaques: {foreign:?}"
    );

    let theorems = file_theorems(&env, "ReductionBound");
    assert!(
        theorems.len() >= 60,
        "expected the whole development, found only {} theorems",
        theorems.len()
    );
    let mut failures = Vec::new();
    let mut used = BTreeSet::new();
    for t in &theorems {
        match audit(&env, t) {
            Ok(f) => used.extend(f),
            Err(e) => failures.extend(e),
        }
    }
    assert!(
        failures.is_empty(),
        "axiom audit failed:\n{}",
        failures.join("\n")
    );
    // The audit's output: the foundational axioms the development consumes.
    eprintln!(
        "reduction_bound axiom audit: {} theorems, foundational axioms reached: {:?}",
        theorems.len(),
        used
    );
}

/// The audit must catch what it is there to catch.
#[test]
fn reduction_bound_audit_catches_axioms_and_sorry() {
    let mut env = Environment::with_prelude();
    let src = r#"
namespace RBAuditControl
axiom bogus : (2 : Nat) = 3
theorem usesAxiom : (2 : Nat) = 3 := bogus
theorem usesSorry : (2 : Nat) = 3 := sorry
end RBAuditControl
"#;
    // Elaboration of the sorry may be reported as a failure; the audit is what is tested.
    let _ = elaborate_into(&mut env, src);
    let ax = Name::from_string("RBAuditControl.usesAxiom");
    assert!(
        env.get_const(&ax).is_some(),
        "control theorem must register"
    );
    assert!(
        audit(&env, &ax).is_err(),
        "an axiom-backed theorem must fail the audit"
    );
    let so = Name::from_string("RBAuditControl.usesSorry");
    assert!(
        env.get_const(&so).is_some(),
        "the sorry control must register (as sorryAx)"
    );
    assert!(
        audit(&env, &so).is_err(),
        "a sorry-backed theorem must fail the audit"
    );
}

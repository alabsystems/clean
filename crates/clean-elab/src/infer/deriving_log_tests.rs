// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A failed `deriving` class leaves its type declared, through the module
//! driver every frontend runs (parse → elaborate → register → per-leaf
//! verdict) on the builtin prelude a Mathlib-free Lean 4.8 file gets.
//!
//! Every source below was run through the pinned Lean 4.8.0 binary as an
//! oracle (2026-09-30): each `Passed` here is a declaration Lean accepts, and
//! each widening has a negative control Lean rejects. The field types are
//! function types, which have no `Repr` / `BEq` / `DecidableEq` in Lean or
//! in any prelude Clean ships, so the failures pinned here cannot close by a
//! prelude gaining an instance.

use crate::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment, module_file_context,
    parse_module, DeclBudgetScope, DeclVerdict, DriverOptions, EnvironmentSetup, ModuleReport,
    VerdictKind,
};
use clean_kernel::{Environment, Name};
use std::path::Path;

fn check_module(source: &str) -> (ModuleReport, Environment) {
    let _lock = module_elaboration_lock();
    let path = Path::new("DerivingLogFixture.lean");
    let mut env = module_environment(EnvironmentSetup::default()).expect("check environment");
    let _budget = DeclBudgetScope::enter(0);
    let parsed = parse_module(path, source).1.expect("fixture parses");
    let mut file_ctx = module_file_context(path);
    let report = elaborate_decls(
        &mut env,
        &parsed.decls,
        source,
        &mut file_ctx,
        DriverOptions::default(),
        &mut (),
    );
    (report, env)
}

fn verdict<'r>(report: &'r ModuleReport, name: &str) -> &'r DeclVerdict {
    report
        .verdicts
        .iter()
        .find(|v| v.name == name)
        .unwrap_or_else(|| panic!("no verdict for `{name}` in {:#?}", report.verdicts))
}

fn assert_passed(report: &ModuleReport, name: &str) {
    let v = verdict(report, name);
    assert_eq!(v.kind, VerdictKind::Passed, "`{name}` must pass: {v:#?}");
}

fn assert_refused(report: &ModuleReport, name: &str) {
    let v = verdict(report, name);
    assert_ne!(
        v.kind,
        VerdictKind::Passed,
        "`{name}` must be refused: {v:#?}"
    );
}

/// The logged failure of `class` on `type_name`: its own failed verdict, at
/// the declaration's line, naming the instance it would have declared.
fn assert_class_failed(
    report: &ModuleReport,
    type_name: &str,
    class: &'static str,
    line: u32,
    reason: &str,
) {
    let instance = crate::derive::builtin_instance_name(&Name::from_string(type_name), class);
    let v = verdict(report, &instance.to_string());
    assert_eq!(v.kind, VerdictKind::ElaborationFailed, "{v:#?}");
    assert_eq!(v.line, Some(line), "{v:#?}");
    let detail = v.detail.as_deref().unwrap_or_default();
    assert!(detail.contains(reason), "{detail}");
}

const W: &str = "structure W where\n  f : Nat → Nat\n  n : Nat\n  deriving Repr\n\
                 def useW (w : W) : Nat := w.f w.n\n\
                 def mkW : W := { f := id, n := 3 }\n";

#[test]
fn test_deriving_failed_class_structure_still_declared_passes() {
    let source = format!("{W}theorem mkW_use : useW mkW = 3 := rfl\n");
    let (report, env) = check_module(&source);
    assert_passed(&report, "W");
    assert_class_failed(
        &report,
        "W",
        "Repr",
        1,
        "cannot synthesize Repr for field `f`",
    );
    for name in ["useW", "mkW", "mkW_use"] {
        assert_passed(&report, name);
    }
    assert_eq!(report.verdicts.len(), 5, "{:#?}", report.verdicts);
    assert!(env.get_const(&Name::from_string("W.mk")).is_some());
    let instance = crate::derive::builtin_instance_name(&Name::from_string("W"), "Repr");
    assert!(
        env.get_const(&instance).is_none(),
        "a failed class registers no instance"
    );
}

#[test]
fn test_deriving_failed_class_structure_false_statement_refused() {
    // Lean 4.8.0: `type mismatch` on both.
    let source = format!(
        "{W}theorem mkW_bad : useW mkW = 4 := rfl\n\
         def badLit : W := {{ f := id, n := true }}\n"
    );
    let (report, _) = check_module(&source);
    assert_passed(&report, "mkW");
    assert_refused(&report, "mkW_bad");
    assert_refused(&report, "badLit");
}

/// trust-ir `Proofs/AggregateProps.lean`'s `TypingEnv`: the literal and the
/// `with` update failed as "struct literal requires type annotation or
/// expected type" and "expected structure type, got FVar(FVarId(0))" because
/// the structure was never declared.
#[test]
fn test_deriving_failed_class_struct_literal_and_update_in_namespace_passes() {
    let source = "namespace N\n\
                  structure TypingEnv where\n  tys : Nat → Option Nat\n  records : Nat → Option Bool\n  deriving Repr\n\
                  namespace TypingEnv\n\
                  def empty : TypingEnv :=\n  { tys := fun _ => none,\n    records := fun _ => none }\n\
                  def withTy (e : TypingEnv) (id : Nat) (t : Nat) : TypingEnv :=\n  { e with tys := fun id' => if id' = id then some t else e.tys id' }\n\
                  end TypingEnv\n\
                  theorem withTy_hit : (TypingEnv.empty.withTy 2 7).tys 2 = some 7 := rfl\n\
                  theorem withTy_bad : (TypingEnv.empty.withTy 2 7).tys 3 = some 7 := rfl\n\
                  end N\n";
    let (report, _) = check_module(source);
    assert_passed(&report, "N.TypingEnv");
    assert_class_failed(
        &report,
        "N.TypingEnv",
        "Repr",
        2,
        "cannot synthesize Repr for field `tys`",
    );
    for name in ["N.TypingEnv.empty", "N.TypingEnv.withTy", "N.withTy_hit"] {
        assert_passed(&report, name);
    }
    // Lean 4.8.0: `type mismatch`.
    assert_refused(&report, "N.withTy_bad");
}

/// Lean's `Repr` handler logs its failure (`elabCommand` is `withLogging`),
/// so `BEq` after it in the clause is still derived.
#[test]
fn test_deriving_logged_class_failure_continues_clause_passes() {
    let source = "structure NoRepr where\n  x : Nat\n  deriving BEq\n\
                  structure V where\n  a : NoRepr\n  deriving Repr, BEq\n\
                  def vBEq : BEq V := inferInstance\n";
    let (report, _) = check_module(source);
    assert_passed(&report, "V");
    assert_class_failed(
        &report,
        "V",
        "Repr",
        4,
        "cannot synthesize Repr for field `a`",
    );
    assert_passed(&report, "vBEq");
}

/// Lean's `Inhabited` handler THROWS when it fails, which ends the clause:
/// `Repr E` is never derived (Lean 4.8.0: `failed to synthesize instance
/// Repr E`), although Clean's inductive `Repr` handler would derive it.
#[test]
fn test_deriving_thrown_class_failure_ends_clause_refused() {
    let source = "inductive E where\n  | mk (x : Empty)\n  deriving Inhabited, Repr\n\
                  def mkE (x : Empty) : E := .mk x\n\
                  def rE : Repr E := inferInstance\n";
    let (report, env) = check_module(source);
    assert_passed(&report, "E");
    assert_class_failed(&report, "E", "Inhabited", 1, "Inhabited");
    assert_passed(&report, "mkE");
    assert_refused(&report, "rE");
    assert_class_never_ran(&report, &env, "E", "Repr");
}

/// `class` never ran for `type_name`: it registered no instance AND left no
/// failed verdict — so the clause ended before it, whatever Clean's own
/// handler for it could have derived.
fn assert_class_never_ran(
    report: &ModuleReport,
    env: &Environment,
    type_name: &str,
    class: &'static str,
) {
    let instance = crate::derive::builtin_instance_name(&Name::from_string(type_name), class);
    assert!(
        env.get_const(&instance).is_none(),
        "the clause ended before `{class}`"
    );
    assert!(
        report
            .verdicts
            .iter()
            .all(|v| v.name != instance.to_string()),
        "`{class}` must never have run: {:#?}",
        report.verdicts
    );
}

/// An inductive survives its failed class too. Lean's own `DecidableEq`
/// failure here is logged and its instance added with `sorryAx` as error
/// recovery, so `inferInstance` finds one in Lean; Clean adds none and the
/// use is refused — never an instance without a proof.
#[test]
fn test_deriving_failed_class_inductive_still_declared_passes() {
    let source = "inductive I where\n  | a (f : Nat → Nat)\n  | b\n  deriving DecidableEq\n\
                  def useI : I := I.b\n\
                  theorem useI_b : useI = I.b := rfl\n\
                  theorem useI_bad : useI = I.a id := rfl\n\
                  def dI : DecidableEq I := inferInstance\n";
    let (report, _) = check_module(source);
    assert_passed(&report, "I");
    assert_class_failed(&report, "I", "DecidableEq", 1, "DecidableEq");
    assert_passed(&report, "useI");
    assert_passed(&report, "useI_b");
    // Lean 4.8.0: `type mismatch`.
    assert_refused(&report, "useI_bad");
    assert_refused(&report, "dI");
}

/// Lean's `DecidableEq` handler elaborates its generated commands through the
/// logging `elabCommand` on a type that is not nested (`mkDecEq`), so a
/// failure there leaves the rest of the clause running: `Repr` after it is
/// still derived. Pinned v4.8.0: only the two `Decidable (a = b)` errors.
#[test]
fn test_deriving_flat_decidable_eq_failure_continues_clause_passes() {
    let source = "structure A where\n  x : Nat\n  deriving Repr\n\
                  structure V where\n  a : A\n  n : Nat\n  deriving DecidableEq, Repr\n\
                  def rV : Repr V := inferInstance\n\
                  inductive W where\n  | mk (a : A)\n  | z\n  deriving DecidableEq, Repr\n\
                  def rW : Repr W := inferInstance\n";
    let (report, env) = check_module(source);
    for name in ["A", "V", "W", "rV", "rW"] {
        assert_passed(&report, name);
    }
    assert_class_failed(&report, "V", "DecidableEq", 4, "DecidableEq");
    assert_class_failed(&report, "W", "DecidableEq", 9, "DecidableEq");
    for ty in ["V", "W"] {
        let decidable = crate::derive::builtin_instance_name(&Name::from_string(ty), "DecidableEq");
        assert!(
            env.get_const(&decidable).is_none(),
            "a failed class registers no instance"
        );
    }
}

/// On a NESTED type Lean's `DecidableEq` handler declines (`mkDecEq` returns
/// `false`) and the default handler throws ("default handlers have not been
/// implemented yet"), which ends the clause: neither `DecidableEq T` nor
/// `Repr T` is derived (pinned v4.8.0: `failed to synthesize instance Repr
/// T`). `List T` is the shape Clean's own nested `DecidableEq` builder COULD
/// derive, and `Repr` one its inductive handler could, so this fails if the
/// refusal ever depends on what Clean's handlers manage; `Array T` is the
/// shape where they cannot.
#[test]
fn test_deriving_nested_decidable_eq_failure_ends_clause_refused() {
    for container in ["List", "Array"] {
        let source = format!(
            "inductive T where\n  | leaf\n  | node (xs : {container} T)\n  deriving DecidableEq, Repr\n\
             def rT : Repr T := inferInstance\n\
             def dT : DecidableEq T := inferInstance\n"
        );
        let (report, env) = check_module(&source);
        assert_passed(&report, "T");
        assert_class_failed(
            &report,
            "T",
            "DecidableEq",
            1,
            "default handlers have not been implemented yet",
        );
        assert_refused(&report, "rT");
        assert_refused(&report, "dT");
        let decidable =
            crate::derive::builtin_instance_name(&Name::from_string("T"), "DecidableEq");
        assert!(
            env.get_const(&decidable).is_none(),
            "{container}: Lean derives no DecidableEq for a nested type"
        );
        assert_class_never_ran(&report, &env, "T", "Repr");
    }
}

/// A NON-nested type whose field holds ANOTHER type under `List` keeps
/// `DecidableEq` (positive control for the nesting test above; pinned
/// v4.8.0 derives it).
#[test]
fn test_deriving_flat_list_field_decidable_eq_passes() {
    let source = "structure P where\n  x : Nat\n  deriving DecidableEq\n\
                  structure Q where\n  xs : List P\n  n : Nat\n  deriving DecidableEq\n\
                  def dQ : DecidableEq Q := inferInstance\n";
    let (report, _) = check_module(source);
    for name in ["P", "Q", "dQ"] {
        assert_passed(&report, name);
    }
}

/// Negative control: a class NAME that does not resolve is not a failed
/// handler. Lean resolves the whole clause (`getOptDerivingClasses`) before
/// it elaborates the type, so the type is never added and every use of it
/// fails. Pinned v4.8.0: `unknown constant 'UnknownClass'`, then errors at
/// `p0` and `pt`.
#[test]
fn test_deriving_unknown_class_structure_undeclared_refused() {
    let source = "structure Point where\n  x : Nat\n  deriving Repr, UnknownClass\n\
                  def p0 : Point := ⟨1⟩\n\
                  theorem pt : p0.x = 1 := rfl\n";
    let (report, env) = check_module(source);
    for name in ["Point", "p0", "pt"] {
        assert_refused(&report, name);
    }
    let detail = verdict(&report, "Point")
        .detail
        .as_deref()
        .unwrap_or_default();
    assert!(detail.contains("UnknownClass"), "{detail}");
    assert!(env.get_const(&Name::from_string("Point")).is_none());
    assert!(env.get_const(&Name::from_string("Point.mk")).is_none());
}

/// Negative control, inductive form: an unknown class anywhere in the
/// clause, even before a class that resolves, leaves the type undeclared.
/// Pinned v4.8.0: `unknown constant 'Nope'`, then `unknown identifier 'J.a'`.
#[test]
fn test_deriving_unknown_class_inductive_undeclared_refused() {
    let source = "inductive J where\n  | a\n  | b\n  deriving Nope, Repr\n\
                  def j0 : J := J.a\n\
                  theorem jt : j0 = J.a := rfl\n";
    let (report, env) = check_module(source);
    for name in ["J", "j0", "jt"] {
        assert_refused(&report, name);
    }
    let detail = verdict(&report, "J").detail.as_deref().unwrap_or_default();
    assert!(detail.contains("Nope"), "{detail}");
    assert!(env.get_const(&Name::from_string("J")).is_none());
}

/// A failed handler leaves nothing behind for the next class or the next
/// declaration: every piece of state term elaboration can change is put back
/// by [`DeclarationRollback`], not only metavariables and locals.
#[test]
fn test_derive_rollback_restores_state_a_failed_handler_changed() {
    use clean_kernel::{Expr, ExprKind};
    use clean_parser::SurfaceName;

    let env = Environment::with_prelude();
    let mut ctx = super::ElabCtx::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let kept = ctx.fresh_fvar();
    ctx.push_local_let_with_fvar(
        SurfaceName::from_name(Name::from_string("kept")),
        kept,
        nat.clone(),
        Expr::nat_lit(23),
    );

    let rollback = super::DeclarationRollback::take(&ctx);
    // What a handler that elaborated part of a term and then failed leaves.
    let leaked = ctx.fresh_fvar();
    ctx.push_local_let_with_fvar(
        SurfaceName::from_name(Name::from_string("leak")),
        leaked,
        nat.clone(),
        Expr::nat_lit(29),
    );
    ctx.push_local_instance(leaked, nat.clone());
    ctx.instance_cache.insert("Leak".to_string(), nat.clone());
    ctx.universe_params
        .push(SurfaceName::from_name(Name::from_string("u_leak")));
    ctx.pending_level_assigns
        .borrow_mut()
        .push((Name::from_string("u_leak"), clean_kernel::Level::zero()));
    ctx.auto_implicits.push((
        SurfaceName::from_name(Name::from_string("α")),
        leaked,
        nat.clone(),
    ));
    ctx.auto_implicit_lookup
        .insert(SurfaceName::from_name(Name::from_string("α")), leaked);
    ctx.postponed_open_carrier_instances
        .push((nat.clone(), nat.clone()));
    ctx.collected_inline.push(Name::from_string("leak"));
    ctx.collected_simp_attrs.push((
        Name::from_string("leak"),
        clean_kernel::env::SimpPriority::default(),
    ));
    let meta = ctx.fresh_meta(nat.clone());

    rollback.restore(&mut ctx);

    assert_eq!(ctx.locals.len(), 1, "only `kept` survives");
    assert_eq!(ctx.locals.let_value(kept), Some(&Expr::nat_lit(23)));
    assert!(ctx.locals.let_value(leaked).is_none());
    assert!(ctx.local_instances.is_empty());
    assert!(ctx.instance_cache.is_empty());
    assert!(ctx.universe_params.is_empty());
    assert!(ctx.pending_level_assigns.borrow().is_empty());
    assert!(ctx.auto_implicits.is_empty());
    assert!(ctx.auto_implicit_lookup.is_empty());
    assert!(ctx.postponed_open_carrier_instances.is_empty());
    assert!(ctx.collected_inline.is_empty());
    assert!(ctx.collected_simp_attrs.is_empty());
    let ExprKind::FVar(meta_fvar) = meta.kind() else {
        panic!("a fresh metavariable is an fvar: {meta}");
    };
    let meta_id = crate::unify::MetaState::from_fvar(*meta_fvar).expect("meta id");
    assert!(
        ctx.metas.get(meta_id).is_none(),
        "the handler's metavariable is gone"
    );
}

/// KNOWN DIVERGENCE — ACCEPTED, LEAN REFUSES — pinned so it fails loudly the
/// day it closes (ledger class (91)). The type stays declared after a class
/// fails, and the failed class registers NO instance, so ordinary resolution
/// of that class at the type finds whatever else is in scope. Pinned v4.8.0
/// derives `BEq` for `Pf` (a proof field needs no `BEq`; `#synth BEq Pf` is
/// `instBEqPf`), so `==` at `Pf` compares `n`: `eqP_ne` checks and `eqP_true`
/// is `type mismatch`. Clean's `BEq` handler refuses the proof field, a
/// logged failure, and `==` resolves to the low-priority catch-all, so the
/// two verdicts swap. (Where Lean's handler itself fails it registers the
/// instance with `sorryAx`, which shadows such a fallback; Clean never
/// registers a `sorry`.) The file still fails on the clause either way.
#[test]
fn test_deriving_failed_class_fallback_instance_stands_in_known_divergence() {
    let source = "instance (priority := low) beqFallback {α : Type} : BEq α := ⟨fun _ _ => true⟩\n\
                  structure Pf where\n  n : Nat\n  h : n = n\n  deriving BEq\n\
                  def eqP (x y : Pf) : Bool := x == y\n\
                  theorem eqP_true : eqP ⟨1, rfl⟩ ⟨2, rfl⟩ = true := rfl\n\
                  theorem eqP_ne : eqP ⟨1, rfl⟩ ⟨2, rfl⟩ = false := rfl\n";
    let (report, env) = check_module(source);
    assert_passed(&report, "Pf");
    assert_class_failed(&report, "Pf", "BEq", 2, "BEq");
    assert_passed(&report, "eqP");
    let beq = crate::derive::builtin_instance_name(&Name::from_string("Pf"), "BEq");
    assert!(env.get_const(&beq).is_none(), "`{beq}` must not register");
    let value = env
        .get_const(&Name::from_string("eqP"))
        .and_then(|c| c.value.clone())
        .expect("eqP has a value");
    let mut names = std::collections::HashSet::new();
    value.collect_constants_into(&mut names);
    assert!(
        names.iter().any(|n| n.to_string().ends_with("beqFallback")),
        "the fallback instance stands in for the failed one: {value}"
    );
    // ACCEPTED where Lean refuses, and refused where Lean accepts.
    assert_passed(&report, "eqP_true");
    assert_refused(&report, "eqP_ne");
}

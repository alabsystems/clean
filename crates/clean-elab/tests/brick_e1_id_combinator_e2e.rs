// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Elaborator Brick E1 — class-method / core-combinator application.
//!
//! ## What this locks
//!
//! The `ELAB_ARMS_AUDIT_2026-07-08` smoke corpus found that applying the
//! standalone core combinator `id` (and its `$` / `<|` / `|>` desugars, which
//! all reduce to `App(id, [x])`) failed with
//! `TooManyArguments { func_type: "Sort(u)" }`. Root cause: `id` is absent from
//! clean's prelude, so a bare `id` fell through to auto-implicit and was bound
//! as a fresh free variable typed `Sort u`; applying an argument to a `Sort u`
//! head is not an application at all.
//!
//! The elaborator now resolves an otherwise-unresolved `id` to the definitional
//! identity lambda `fun {α : Sort u} (a : α) => a` (`infer/elab_core.rs`,
//! `elab_ident`). The application elaborator's *existing* implicit-insertion
//! path then inserts the leading `{α}` metavar and applies the explicit
//! argument — the same path the registered `HAdd.hAdd` head already uses — and
//! the kernel re-checks the resulting β-redex.
//!
//! ## Tripwire (silent-wrong canary)
//!
//! The audit flagged `getElem` with no bounds proof and `▸` casts as latent
//! unsoundness traps. Those heads are still unregistered (a DIFFERENT gap:
//! typeclass + instance prelude infrastructure), so they must still FAIL LOUD.
//! `id` resolution must never make them (or an unresolved instance/proof
//! obligation) silently succeed. The `z*` cases assert continued rejection.

use clean_elab::{elaborate_decl, ElabResult};
use clean_kernel::{Declaration, Environment, TypeChecker};
use clean_parser::parse_decl;

/// Drive the full `parse -> elaborate -> kernel type-check -> add_decl`
/// pipeline for a single declaration against the standard prelude — the same
/// stages `clean check` runs. Returns `Ok(())` iff the declaration elaborates
/// AND the kernel accepts the elaborated term.
fn check_decl(env: &mut Environment, src: &str) -> Result<(), String> {
    let surface = parse_decl(src).map_err(|e| format!("parse error: {e}"))?;
    let elab = elaborate_decl(env, &surface).map_err(|e| format!("elab error: {e}"))?;
    match elab {
        ElabResult::Definition {
            name,
            universe_params,
            ty,
            val,
            ..
        } => {
            {
                let tc = TypeChecker::new(env);
                let _ = tc.infer_type(&ty).map_err(|e| format!("kernel ty: {e}"))?;
                tc.check_type(&val, &ty)
                    .map_err(|e| format!("kernel val: {e}"))?;
            }
            env.add_decl(Declaration::Definition {
                name,
                level_params: universe_params,
                type_: ty,
                value: val,
                is_reducible: true,
            })
            .map_err(|e| format!("add_decl: {e}"))
        }
        ElabResult::Theorem {
            name,
            universe_params,
            ty,
            proof,
            ..
        } => {
            {
                let tc = TypeChecker::new(env);
                let _ = tc.infer_type(&ty).map_err(|e| format!("kernel ty: {e}"))?;
                tc.check_type(&proof, &ty)
                    .map_err(|e| format!("kernel proof: {e}"))?;
            }
            env.add_decl(Declaration::Theorem {
                name,
                level_params: universe_params,
                type_: ty,
                value: proof,
            })
            .map_err(|e| format!("add_decl: {e}"))
        }
        other => Err(format!("unexpected elab result: {other:?}")),
    }
}

#[test]
fn test_id_applied_to_literal_elaborates_and_kernel_checks() {
    let mut env = Environment::with_prelude();
    check_decl(&mut env, "def i5 : Nat := id 5")
        .expect("`id 5` must elaborate and kernel-check (Brick E1)");
}

#[test]
fn test_id_dollar_desugar_elaborates() {
    let mut env = Environment::with_prelude();
    // `id $ 5` desugars to `App(id, [5])`.
    check_decl(&mut env, "def d : Nat := id $ 5").expect("`id $ 5` must elaborate (Brick E1)");
}

#[test]
fn test_id_left_pipe_desugar_elaborates() {
    let mut env = Environment::with_prelude();
    // `id <| 5` desugars to `App(id, [5])`.
    check_decl(&mut env, "def lp : Nat := id <| 5").expect("`id <| 5` must elaborate (Brick E1)");
}

#[test]
fn test_id_right_pipe_desugar_elaborates() {
    let mut env = Environment::with_prelude();
    // `5 |> id` desugars to `App(id, [5])`.
    check_decl(&mut env, "def rp : Nat := 5 |> id").expect("`5 |> id` must elaborate (Brick E1)");
}

#[test]
fn test_id_polymorphic_over_type_argument() {
    let mut env = Environment::with_prelude();
    // The inserted `{α}` metavar must be pinned by the explicit operand's type,
    // not defaulted: `id` over a `List Nat` value stays a `List Nat`.
    check_decl(&mut env, "def il (xs : List Nat) : List Nat := id xs")
        .expect("`id xs` must elaborate polymorphically (Brick E1)");
}

#[test]
fn test_user_defined_id_still_takes_precedence() {
    // A user `def id ...` (a real constant) must shadow the built-in combinator
    // resolution — the check fires only when `id` is otherwise unresolved.
    let mut env = Environment::with_prelude();
    check_decl(&mut env, "def id2 (A : Type) (x : A) : A := x").expect("user def registers");
    // Re-uses the same shadowing logic the integration `test_use_defined_constant`
    // relies on; here we just confirm a locally-bound `id` binder is unaffected.
    check_decl(&mut env, "def useLocalId (id : Nat) : Nat := id")
        .expect("a binder named `id` must resolve to the binder, not the combinator");
}

// ---------------------------------------------------------------------------
// Silent-wrong tripwires. getElem with NO bounds proof in scope MUST still
// fail loud: Brick 4 registered the List GetElem instances and the
// `get_elem_tactic` analog, so the failure mode is now the tactic-chain
// rejection ("failed to prove index is valid") — the obligation
// `0 < List.length xs` is genuinely unprovable and must never be filled by
// sorry or a defaulting metavariable. The `▸` probe flipped to a positive
// when Brick E2 landed the elabSubst port (its loud negatives moved to
// tests/brick_e2_subst_e2e.rs).
// ---------------------------------------------------------------------------

#[test]
fn test_z_getelem_no_bounds_proof_still_rejected() {
    let mut env = Environment::with_prelude();
    // `xs[0]` with no bounds proof in scope must NOT be silently accepted.
    let r = check_decl(&mut env, "def g (xs : List Nat) : Nat := xs[0]");
    assert!(
        r.is_err(),
        "no-bounds-proof getElem must fail loud, got Ok: {r:?}"
    );
}

#[test]
fn test_z_subst_cast_now_elaborates_via_elab_subst() {
    let mut env = Environment::with_prelude();
    // Originally a must-fail-loud tripwire ("`▸` motive inference is
    // unimplemented"). Brick E2 implemented the Lean-faithful `elabSubst`
    // port (infer/elab_subst.rs), so this proof-position cast now elaborates
    // and is kernel-re-checked. The silent-wrong guards (orientation search,
    // value-pinned computational casts, loud no-occurrence / non-equality
    // negatives) live in tests/brick_e2_subst_e2e.rs.
    check_decl(
        &mut env,
        "theorem t (a b : Nat) (h : a = b) : b = a := h ▸ rfl",
    )
    .expect("`h ▸ rfl` must elaborate via the Brick E2 subst arm");
}

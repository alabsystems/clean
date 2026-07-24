// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real-body `DecidableEq` construction for monomorphic enum inductives
//! (nullary constructors, no type parameters). Fixes #3432.
//!
//! Split out of `infer::derive::inductive` to keep that module under the
//! 500-line size limit.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, Level};
use clean_parser::{SurfaceCtor, SurfaceExpr};

/// Return `true` iff every constructor in `ctors` is nullary
/// (its surface type is not a `Pi` or `Arrow`, i.e. takes no fields).
///
/// Used by `derive_decidable_eq_inductive` to decide whether the multi-ctor
/// enum path (which builds a real `casesOn` / `noConfusion` proof term
/// without needing per-field decEq calls) is applicable. Constructors with
/// fields require a proof-producing field or recursive builder; unsupported
/// shapes fail closed.
pub(super) fn all_ctors_nullary(ctors: &[SurfaceCtor]) -> bool {
    ctors.iter().all(|c| ctor_is_nullary(&c.ty))
}

/// Is this surface ctor type nullary (no `Pi` / `Arrow` binder above the
/// return type)? Peels `Paren` / `Ascription` wrappers.
fn ctor_is_nullary(ty: &SurfaceExpr) -> bool {
    match ty {
        SurfaceExpr::Pi(_, _, _) | SurfaceExpr::Arrow(_, _, _) => false,
        SurfaceExpr::Paren(_, inner) | SurfaceExpr::Ascription(_, inner, _) => {
            ctor_is_nullary(inner)
        }
        _ => true,
    }
}

/// Build the body of a monomorphic enum `DecidableEq` instance as a real
/// decision procedure (not a `sorry`-backed stub). This enables
/// `decide (x = y)` to reduce to `Bool.true` / `Bool.false` at the kernel
/// (#3432).
///
/// The body is constructed at de Bruijn depth 2 — i.e. inside the outer
/// `λ (a : X) (b : X)` lambdas where `a = bvar(1)` and `b = bvar(0)`:
///
/// ```text
/// X.casesOn.{1} (λ a' : X => Decidable (@Eq X a' b))
///   a
///   minor_0            -- a = c_0
///   minor_1            -- a = c_1
///   ...
///   minor_{n-1}        -- a = c_{n-1}
/// ```
///
/// where `minor_i` discriminates on `b`:
///
/// ```text
/// X.casesOn.{1} (λ b' : X => Decidable (@Eq X c_i b'))
///   b
///   (if i == j then isTrue(refl c_i) else isFalse(noConfusion))
///   ...
/// ```
///
/// `noConfusion` produces `False` for distinct nullary constructors via
/// the kernel-generated `noConfusionType` iota reduction (see
/// `clean-kernel::env::inductive_no_confusion`).
///
/// # Preconditions
/// - Monomorphic (`num_params == 0`)
/// - All ctors nullary (no field arguments)
/// - Any constructor count, including empty and singleton inductives
///
/// # Universe levels
/// All levels are written explicitly (no `Level::Param`) so
/// `concretize_monomorphic_instance` leaves them untouched:
/// - `X.casesOn.{Succ(Zero)}` — motive returns `Decidable _ : Sort 1`
/// - `X.noConfusion.{Zero}` — applied to `P = False : Prop`
/// - `@Eq.{Succ(Zero)}`, `@Eq.refl.{Succ(Zero)}` — over `X : Type 0 = Sort 1`
pub(super) fn build_body(ind_name: &Name, ctor_names: &[Name], ind_type: &Expr) -> Expr {
    // Level 1 = Succ(Zero); used for casesOn motive universe, Eq.{u}, Eq.refl.{u}.
    let level_one = Level::succ(Level::zero());
    let cases_on_name = Name::from_string(&format!("{ind_name}.casesOn"));
    let no_confusion_name = Name::from_string(&format!("{ind_name}.noConfusion"));

    // Fully explicit Eq / Eq.refl constants at the enum's universe level
    // (X : Type 0 means u = 1 in `Eq.{u}` / `Eq.refl.{u}`).
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![level_one.clone()]);
    let eq_refl_const = Expr::const_(Name::from_string("Eq.refl"), vec![level_one.clone()]);

    // `Decidable`, `Decidable.isTrue`, `Decidable.isFalse`, and `False`
    // are universe-monomorphic in the clean prelude.
    let decidable_const = Expr::const_(Name::from_string("Decidable"), vec![]);
    let decidable_is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
    let decidable_is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
    let false_const = Expr::const_(Name::from_string("False"), vec![]);

    // Outer motive: λ a' : X => Decidable (@Eq X a' b)
    // Inside the motive lambda: a' = bvar(0), b = bvar(1) (shifted by 1
    // from body depth 2).
    let outer_motive = {
        let eq_prop = Expr::app(
            Expr::app(
                Expr::app(eq_const.clone(), ind_type.clone()),
                Expr::bvar(0), // a'
            ),
            Expr::bvar(1), // b (lifted through the motive lambda)
        );
        let decidable_body = Expr::app(decidable_const.clone(), eq_prop);
        Expr::lam(BinderInfo::Default, ind_type.clone(), decidable_body)
    };

    // Build each outer minor: for a = c_i, do inner casesOn on b.
    let mut outer_minors: Vec<Expr> = Vec::with_capacity(ctor_names.len());
    for (i, outer_ctor_name) in ctor_names.iter().enumerate() {
        // `c_i` as a constant with empty levels (ctors of a monomorphic
        // inductive are themselves monomorphic).
        let ctor_i_const = Expr::const_(outer_ctor_name.clone(), vec![]);

        // Inner motive: λ b' : X => Decidable (@Eq X c_i b')
        // Inside the lambda: b' = bvar(0); c_i is a closed constant, so no
        // index shifting is needed for it.
        let inner_motive = {
            let eq_prop = Expr::app(
                Expr::app(
                    Expr::app(eq_const.clone(), ind_type.clone()),
                    ctor_i_const.clone(),
                ),
                Expr::bvar(0), // b'
            );
            let decidable_body = Expr::app(decidable_const.clone(), eq_prop);
            Expr::lam(BinderInfo::Default, ind_type.clone(), decidable_body)
        };

        // Inner minors: one per ctor c_j of b.
        let mut inner_minors: Vec<Expr> = Vec::with_capacity(ctor_names.len());
        for (j, inner_ctor_name) in ctor_names.iter().enumerate() {
            let ctor_j_const = Expr::const_(inner_ctor_name.clone(), vec![]);

            // Eq proposition `@Eq X c_i c_j` (closed, no bvars).
            let eq_prop_ij = Expr::app(
                Expr::app(
                    Expr::app(eq_const.clone(), ind_type.clone()),
                    ctor_i_const.clone(),
                ),
                ctor_j_const.clone(),
            );

            let inner_minor = if i == j {
                // @Decidable.isTrue (@Eq X c_i c_i) (@Eq.refl X c_i)
                let eq_refl_ci = Expr::app(
                    Expr::app(eq_refl_const.clone(), ind_type.clone()),
                    ctor_i_const.clone(),
                );
                Expr::app(Expr::app(decidable_is_true.clone(), eq_prop_ij), eq_refl_ci)
            } else {
                // @Decidable.isFalse (@Eq X c_i c_j)
                //   (λ h : @Eq X c_i c_j => @X.noConfusion.{0} False c_i c_j h)
                //
                // Inside the `h`-binder: bvar(0) = h. c_i / c_j are closed.
                let no_conf_call = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(no_confusion_name.clone(), vec![Level::zero()]),
                                false_const.clone(),
                            ),
                            ctor_i_const.clone(),
                        ),
                        ctor_j_const.clone(),
                    ),
                    Expr::bvar(0), // h
                );
                let neg_witness = Expr::lam(BinderInfo::Default, eq_prop_ij.clone(), no_conf_call);
                Expr::app(
                    Expr::app(decidable_is_false.clone(), eq_prop_ij),
                    neg_witness,
                )
            };
            inner_minors.push(inner_minor);
        }

        // Inner casesOn: `X.casesOn.{1} inner_motive b minor_0 ... minor_{n-1}`
        // At body depth 2 (same as the outer minor), b = bvar(0).
        // Lean-faithful casesOn order: motive, (indices,) major, then minors.
        let mut inner_cases = Expr::const_(cases_on_name.clone(), vec![level_one.clone()]);
        inner_cases = Expr::app(inner_cases, inner_motive);
        inner_cases = Expr::app(inner_cases, Expr::bvar(0)); // b as major
        for inner_minor in inner_minors {
            inner_cases = Expr::app(inner_cases, inner_minor);
        }

        outer_minors.push(inner_cases);
        let _ = i; // silence unused warning
    }

    // Outer casesOn: `X.casesOn.{1} outer_motive a minor_0 ... minor_{n-1}`
    // At body depth 2, a = bvar(1).
    // Lean-faithful casesOn order: motive, (indices,) major, then minors.
    let mut outer_cases = Expr::const_(cases_on_name, vec![level_one]);
    outer_cases = Expr::app(outer_cases, outer_motive);
    outer_cases = Expr::app(outer_cases, Expr::bvar(1)); // a as major
    for outer_minor in outer_minors {
        outer_cases = Expr::app(outer_cases, outer_minor);
    }

    outer_cases
}

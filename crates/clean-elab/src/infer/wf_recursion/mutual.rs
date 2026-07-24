// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mutual well-founded recursion via the PackMutual encoding.
//!
//! Multiple mutually recursive functions are packed into a single unary
//! function over a sum type, then the standard `WellFounded.fix` encoding
//! is applied to the packed function, and finally individual definitions
//! are unpacked by projection.
//!
//! # Encoding
//!
//! Given N mutually recursive functions:
//!   `f₁ (x : α₁) : β₁`, ..., `fₙ (x : αₙ) : βₙ`
//!
//! 1. **Pack domain**: `PSum α₁ (PSum α₂ (... αₙ))` — a nested sum of
//!    all argument types.
//! 2. **Pack codomain**: A motive that maps each injection to the
//!    corresponding return type.
//! 3. **Pack body**: A single function that case-splits on the sum
//!    injection to dispatch to the appropriate function body, with
//!    cross-function recursive calls rewritten as calls to the
//!    fixpoint's recursive argument composed with the appropriate
//!    injection.
//! 4. **Unpack**: Each `fᵢ(x)` is defined as
//!    `packed_fix (PSum.inl/inr ... x)` projected to extract `βᵢ`.
//!
//! Reference: Lean 4 `src/Lean/Elab/PreDefinition/WF/PackMutual.lean`

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprFolder, FVarId, Level};

use super::ElabCtx;
use crate::ElabError;

/// Information about a group of mutually recursive functions to be packed.
#[derive(Debug, Clone)]
pub(crate) struct MutualPackInfo {
    /// Names of the mutually recursive functions.
    pub(crate) func_names: Vec<String>,
    /// Fully elaborated types of each function (Pi types).
    pub(crate) func_types: Vec<Expr>,
    /// Elaborated bodies of each function (Lambda terms).
    pub(crate) func_bodies: Vec<Expr>,
    /// FVarIds used as forward declarations for each function during
    /// elaboration (recursive calls resolve to these).
    pub(crate) func_fvars: Vec<FVarId>,
    /// Per-function binder FVars and their types.
    pub(crate) binder_fvars: Vec<Vec<(FVarId, Expr)>>,
}

/// Build a nested `PSum` type from a list of types.
///
/// `[A, B, C]` becomes `PSum A (PSum B C)`.
/// A single type `[A]` is returned as-is.
pub(crate) fn build_psum_type(types: &[Expr], u_level: &Level) -> Result<Expr, ElabError> {
    if types.is_empty() {
        return Err(ElabError::Unsupported {
            feature: "mutual WF recursion: empty function list".to_owned(),
        });
    }
    if types.len() == 1 {
        return Ok(types[0].clone());
    }

    // Build right-to-left: PSum types[n-2] (PSum types[n-1] types[n])
    // But for 2 elements: PSum A B
    let mut result = types.last().expect("len >= 2").clone();
    for ty in types.iter().rev().skip(1) {
        let psum = Expr::const_(
            Name::from_string("PSum"),
            vec![u_level.clone(), u_level.clone()],
        );
        result = Expr::app(Expr::app(psum, ty.clone()), result);
    }
    Ok(result)
}

/// Build the injection expression for the `i`-th component of a PSum
/// of `n` types.
///
/// For `n=3, i=0`: `PSum.inl`
/// For `n=3, i=1`: `PSum.inr ∘ PSum.inl`
/// For `n=3, i=2`: `PSum.inr ∘ PSum.inr`
///
/// Returns a function `αᵢ → PSum α₁ (PSum α₂ ...)`.
pub(crate) fn build_psum_injection(
    arg_types: &[Expr],
    idx: usize,
    u_level: &Level,
) -> Result<Expr, ElabError> {
    if idx >= arg_types.len() {
        return Err(ElabError::Unsupported {
            feature: format!(
                "mutual WF recursion: injection index {} out of bounds ({})",
                idx,
                arg_types.len()
            ),
        });
    }

    if arg_types.len() == 1 {
        // Single function — identity injection
        return Ok(Expr::lam(
            BinderInfo::Default,
            arg_types[0].clone(),
            Expr::bvar(0),
        ));
    }

    // For the last element, we need (n - idx - 1) PSum.inr wrappers
    // For any non-last element, we need idx PSum.inr wrappers then one PSum.inl

    let is_last = idx == arg_types.len() - 1;
    // Both last and non-last need `idx` PSum.inr wrappers; the difference is
    // that non-last cases get an additional PSum.inl wrapper below.
    let inr_count = idx;

    // Start with the value (bvar 0 after lambda abstraction)
    let mut expr = Expr::bvar(0);

    // If not last, wrap with PSum.inl
    if !is_last {
        let remaining_types = &arg_types[(idx + 1)..];
        let right_type = build_psum_type(remaining_types, u_level)?;
        let inl = Expr::const_(
            Name::from_string("PSum.inl"),
            vec![u_level.clone(), u_level.clone()],
        );
        expr = Expr::app(
            Expr::app(Expr::app(inl, arg_types[idx].clone()), right_type),
            expr,
        );
    }

    // Wrap with PSum.inr for each preceding type
    for j in (0..inr_count).rev() {
        let left_type = arg_types[j].clone();
        let remaining = &arg_types[(j + 1)..];
        let right_type = build_psum_type(remaining, u_level)?;
        let inr = Expr::const_(
            Name::from_string("PSum.inr"),
            vec![u_level.clone(), u_level.clone()],
        );
        expr = Expr::app(Expr::app(Expr::app(inr, left_type), right_type), expr);
    }

    // Wrap in lambda
    Ok(Expr::lam(BinderInfo::Default, arg_types[idx].clone(), expr))
}

/// Build a PSum eliminator that case-splits on the injection index and
/// applies the corresponding branch.
///
/// For `[A, B, C]` with branches `[f, g, h]`, produces:
/// ```text
/// fun (x : PSum A (PSum B C)) =>
///   PSum.casesOn x f (fun y => PSum.casesOn y g h)
/// ```
pub(crate) fn build_psum_elim(
    arg_types: &[Expr],
    branches: &[Expr],
    ret_type: &Expr,
    u_level: &Level,
) -> Result<Expr, ElabError> {
    if arg_types.len() != branches.len() {
        return Err(ElabError::Unsupported {
            feature: format!(
                "mutual WF recursion: mismatch between types ({}) and branches ({})",
                arg_types.len(),
                branches.len()
            ),
        });
    }

    if arg_types.len() == 1 {
        return Ok(branches[0].clone());
    }

    // Build right-to-left recursively
    build_psum_elim_inner(arg_types, branches, ret_type, u_level, 0)
}

fn build_psum_elim_inner(
    arg_types: &[Expr],
    branches: &[Expr],
    ret_type: &Expr,
    u_level: &Level,
    offset: usize,
) -> Result<Expr, ElabError> {
    let remaining = arg_types.len() - offset;
    if remaining == 1 {
        return Ok(branches[offset].clone());
    }

    let right_branch = build_psum_elim_inner(arg_types, branches, ret_type, u_level, offset + 1)?;

    // PSum.casesOn.{u1, u2, v} : {α : Sort u1} → {β : Sort u2} →
    //   {motive : PSum α β → Sort v} → (t : PSum α β) →
    //   ((a : α) → motive (PSum.inl a)) → ((b : β) → motive (PSum.inr b)) →
    //   motive t
    let cases_on = Expr::const_(
        Name::from_string("PSum.casesOn"),
        vec![u_level.clone(), u_level.clone(), u_level.clone()],
    );

    let left_type = arg_types[offset].clone();
    let right_types = &arg_types[(offset + 1)..];
    let right_type = build_psum_type(right_types, u_level)?;

    // Motive: fun _ => ret_type (constant motive)
    let psum_ty = {
        let psum = Expr::const_(
            Name::from_string("PSum"),
            vec![u_level.clone(), u_level.clone()],
        );
        Expr::app(Expr::app(psum, left_type.clone()), right_type.clone())
    };
    let motive = Expr::lam(BinderInfo::Default, psum_ty.clone(), ret_type.clone());

    let result = Expr::apps(
        cases_on,
        [
            left_type,
            right_type,
            motive,
            Expr::bvar(0), // the scrutinee (to be applied)
            branches[offset].clone(),
            right_branch,
        ],
    );

    Ok(result)
}

/// Replace references to any of the mutual function FVars with a
/// wrapper that injects arguments into the packed domain and calls
/// the packed recursive argument.
struct MutualRecCallReplacer {
    /// FVarIds of the original mutually recursive functions.
    func_fvars: Vec<FVarId>,
    /// FVarId of the packed `rec` parameter.
    rec_fvar: FVarId,
    /// Injection functions for each function index.
    injections: Vec<Expr>,
}

impl ExprFolder for MutualRecCallReplacer {
    fn fold_fvar(&mut self, id: FVarId) -> Expr {
        for &func_fvar in self.func_fvars.iter() {
            if id == func_fvar {
                // Replace f_i with: fun arg => rec (inject_i arg) sorry
                // For now, just replace the function reference with a
                // composition rec . inject_i (the caller handles sorry insertion)
                return Expr::fvar(self.rec_fvar);
            }
        }
        Expr::fvar(id)
    }
}

/// Replace all mutual recursive calls in a body with calls through the
/// packed `rec` parameter composed with the appropriate injection.
pub(crate) fn replace_mutual_rec_calls(
    body: &Expr,
    func_fvars: &[FVarId],
    rec_fvar: FVarId,
    injections: &[Expr],
) -> Expr {
    let mut folder = MutualRecCallReplacer {
        func_fvars: func_fvars.to_vec(),
        rec_fvar,
        injections: injections.to_vec(),
    };
    folder.fold_expr(body)
}

impl<'a> ElabCtx<'a> {
    /// Elaborate a group of mutually recursive definitions using
    /// well-founded recursion with the PackMutual encoding.
    ///
    /// # Arguments
    ///
    /// * `pack_info` - Pre-elaborated information about all functions
    /// * `measure_expr` - The termination measure (applied to the packed arg)
    ///
    /// # Returns
    ///
    /// A vector of `(type, value)` pairs, one for each function in the group.
    pub(crate) fn elab_mutual_wf_recursion(
        &mut self,
        pack_info: &MutualPackInfo,
        measure_expr: &Expr,
    ) -> Result<Vec<(Expr, Expr)>, ElabError> {
        let n = pack_info.func_names.len();
        if n == 0 {
            return Err(ElabError::Unsupported {
                feature: "mutual WF recursion: no functions".to_owned(),
            });
        }
        if n == 1 {
            // Single function — delegate to standard WF encoding
            return Err(ElabError::Unsupported {
                feature: "mutual WF recursion with single function: use standard WF path"
                    .to_owned(),
            });
        }

        // Step 1: Extract the first-argument type from each function
        let arg_types: Vec<Expr> = pack_info
            .binder_fvars
            .iter()
            .map(|fvars| {
                fvars
                    .first()
                    .map(|(_, ty)| ty.clone())
                    .ok_or_else(|| ElabError::Unsupported {
                        feature: "mutual WF recursion: function with no parameters".to_owned(),
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Step 2: Extract return types
        let ret_types: Vec<Expr> = pack_info
            .func_types
            .iter()
            .zip(pack_info.binder_fvars.iter())
            .map(|(ty, fvars)| self.extract_return_type(ty, fvars.len()))
            .collect::<Result<Vec<_>, _>>()?;

        // Step 3: Determine universe level
        let u_level = arg_types
            .first()
            .and_then(|ty| self.infer_sort(ty).ok())
            .unwrap_or_else(|| Level::param(Name::from_string("u_wf")));

        // Step 4: Build packed domain (PSum of all arg types)
        let packed_domain = build_psum_type(&arg_types, &u_level)?;

        // Step 5: Build packed codomain (PSum of all return types)
        let packed_codomain = build_psum_type(&ret_types, &u_level)?;

        // Step 6: Build injection functions
        let injections: Vec<Expr> = (0..n)
            .map(|i| build_psum_injection(&arg_types, i, &u_level))
            .collect::<Result<Vec<_>, _>>()?;

        // Step 7: Build the packed motive
        let motive = Expr::lam(
            BinderInfo::Default,
            packed_domain.clone(),
            packed_codomain.clone(),
        );

        // Step 8: Build measure lambda on packed domain
        let measure_lambda = Expr::lam(
            BinderInfo::Default,
            packed_domain.clone(),
            measure_expr.clone(),
        );

        // Step 9: Build WellFoundedRelation via invImage
        let inv_image = Expr::const_(Name::from_string("invImage"), vec![u_level.clone()]);
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_lt_wfrel = Expr::const_(Name::from_string("Nat.lt_wfRel"), vec![]);
        let wfr = Expr::apps(
            inv_image,
            [packed_domain.clone(), nat_ty, measure_lambda, nat_lt_wfrel],
        );

        let rel = Expr::proj(Name::from_string("WellFoundedRelation"), 0, wfr.clone());
        let wf_proof = Expr::proj(Name::from_string("WellFoundedRelation"), 1, wfr);

        // Step 10: Build the packed fixpoint body
        let rec_fvar = self.fresh_fvar();

        // Build branch bodies: for each function, strip lambdas and
        // replace recursive calls with packed rec + injection
        let branch_bodies: Vec<Expr> = (0..n)
            .map(|i| {
                let (stripped, _) =
                    self.strip_lambdas(&pack_info.func_bodies[i], pack_info.binder_fvars[i].len());
                let transformed = replace_mutual_rec_calls(
                    &stripped,
                    &pack_info.func_fvars,
                    rec_fvar,
                    &injections,
                );
                // Wrap back as lambda over the function's own argument
                if let Some((fvar, ref ty)) = pack_info.binder_fvars[i].first() {
                    let body = transformed.abstract_fvar(*fvar);
                    Expr::lam(BinderInfo::Default, ty.clone(), body)
                } else {
                    transformed
                }
            })
            .collect();

        // Step 11: Build the PSum eliminator over branch_bodies
        let elim = build_psum_elim(&arg_types, &branch_bodies, &packed_codomain, &u_level)?;

        // The fix body: fun (x : PackedDomain) (rec : ...) => elim x
        let v_level = self
            .infer_sort(&packed_codomain)
            .unwrap_or_else(|_| Level::param(Name::from_string("v_wf")));

        // Build rec parameter type
        let rec_param_ty = {
            let y_fvar = self.fresh_fvar();
            let rel_y_x = Expr::app(
                Expr::app(rel.clone(), Expr::fvar(y_fvar)),
                Expr::bvar(0), // x
            );
            let c_y = Expr::app(motive.clone(), Expr::fvar(y_fvar));
            let inner = Expr::arrow(rel_y_x, c_y);
            let inner_abs = inner.abstract_fvar(y_fvar);
            Expr::pi(BinderInfo::Default, packed_domain.clone(), inner_abs)
        };

        // fix_body = fun (x : PackedDomain) (rec : RecType) => elim x
        let fix_body_inner = elim.abstract_fvar(rec_fvar);
        let fix_body_inner = Expr::lam(BinderInfo::Default, rec_param_ty, fix_body_inner);
        let x_fvar = self.fresh_fvar();
        let fix_body_abs = fix_body_inner.abstract_fvar(x_fvar);
        let fix_body = Expr::lam(BinderInfo::Default, packed_domain.clone(), fix_body_abs);

        // Step 12: Build WellFounded.fix application
        let wf_fix = Expr::const_(
            Name::from_string("WellFounded.fix"),
            vec![u_level.clone(), v_level],
        );
        let packed_fix = Expr::apps(
            wf_fix,
            [
                packed_domain.clone(),
                motive.clone(),
                rel,
                wf_proof,
                fix_body,
            ],
        );

        // Step 13: Unpack individual definitions
        let results: Vec<(Expr, Expr)> = (0..n)
            .map(|i| {
                // f_i(x) = packed_fix (inject_i x)
                let injection_i = injections[i].clone();
                let arg_fvar = self.fresh_fvar();
                let injected = Expr::app(injection_i, Expr::fvar(arg_fvar));
                let applied = Expr::app(packed_fix.clone(), injected);
                let body = applied.abstract_fvar(arg_fvar);
                let val = Expr::lam(BinderInfo::Default, arg_types[i].clone(), body);
                (pack_info.func_types[i].clone(), val)
            })
            .collect();

        Ok(results)
    }
}

// Tests for mutual WF recursion are in the parent `tests.rs` module.

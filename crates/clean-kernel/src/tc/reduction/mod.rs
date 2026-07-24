// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::expr::{BinderInfo, Expr, ExprKind, LevelVec, Literal};
use crate::inductive::{get_return_type, RecursorArgOrder, RecursorVal};
use crate::level::Level;
use crate::tc::TypeChecker;
use std::sync::Arc;

pub(crate) mod cofib;
pub(crate) mod directed;
pub(crate) mod int;
pub(crate) mod kan;
mod nat;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_iota_edge;
#[cfg(test)]
mod tests_nested_aux_recursor;

pub(crate) use nat::string_lit_to_constructor;

/// Well-known names used in Nat, Bool, and String reduction hot paths.
/// Cached as statics to avoid repeated `Name::from_string` allocation on every call.
/// Follows the same pattern as `crate::quot::names`.
pub(super) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub static NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat"));
    pub static NAT_REC: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.rec"));
    pub static NAT_ZERO: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.zero"));
    pub static NAT_SUCC: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.succ"));
    pub static NAT_PRED: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.pred"));
    pub static NAT_ADD: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.add"));
    pub static NAT_SUB: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.sub"));
    pub static NAT_MUL: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.mul"));
    pub static NAT_DIV: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.div"));
    pub static NAT_MOD: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.mod"));
    pub static NAT_GCD: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.gcd"));
    pub static NAT_POW: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.pow"));
    pub static NAT_BEQ: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.beq"));
    pub static NAT_BLE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.ble"));
    pub static NAT_LAND: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.land"));
    pub static NAT_LOR: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.lor"));
    pub static NAT_XOR: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.xor"));
    pub static NAT_SHIFT_LEFT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Nat.shiftLeft"));
    pub static NAT_SHIFT_RIGHT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Nat.shiftRight"));
    pub static INT_OF_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.ofNat"));
    pub static INT_NEG_SUCC: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.negSucc"));
    pub static INT_ADD: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.add"));
    pub static INT_SUB: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.sub"));
    pub static INT_MUL: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.mul"));
    pub static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
    pub static BOOL_FALSE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));
    pub static STRING_OF_LIST: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.ofList"));
    pub static LIST_NIL: LazyLock<Name> = LazyLock::new(|| Name::from_string("List.nil"));
    pub static LIST_CONS: LazyLock<Name> = LazyLock::new(|| Name::from_string("List.cons"));
    pub static CHAR: LazyLock<Name> = LazyLock::new(|| Name::from_string("Char"));
    pub static CHAR_OF_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Char.ofNat"));
}

impl<'env> TypeChecker<'env> {
    /// Try to apply iota reduction (recursor computation rule).
    ///
    /// For `I.rec params motive minors indices (I.ctor params args)`, reduces to
    /// `minor args rec_results`. Returns `None` if head is not a recursor, not
    /// enough args, major premise is stuck, or constructor doesn't match.
    ///
    /// Preserves definitional equality and types. Supports both argument orders:
    /// `MajorAfterMinors` (standard rec) and `MajorAfterMotive` (recOn style).
    ///
    /// Uses RHS-based reduction (#1406): instantiate level params in the pre-built
    /// `RecursorRule.rhs` lambda, apply params+motives+minors, then fields, then
    /// extras. Matches Lean 4's `inductive_reduce_rec` (inductive.h:104-117).
    pub(super) fn try_iota_reduction(&self, e: &Expr, use_delta: bool) -> Option<Expr> {
        // Early exit: check if head is a Const before collecting args (O(1) vs O(n))
        // This is critical for performance on stuck application chains (#949)
        let head = e.get_app_fn();

        // Check if head is a recursor - exit early if not to avoid O(n) arg collection
        let ExprKind::Const(rec_name, rec_levels) = &head.kind else {
            #[cfg(feature = "debug-whnf")]
            eprintln!("[try_iota_reduction] head is not Const, returning None");
            return None;
        };

        // Now collect args (only after confirming head is a Const)
        let args = e.get_app_args();

        #[cfg(feature = "debug-whnf")]
        eprintln!(
            "[try_iota_reduction] head: {:?}, args.len: {}",
            head,
            args.len()
        );

        let rec_val = self.env.get_recursor(rec_name)?;

        #[cfg(feature = "debug-whnf")]
        eprintln!("[try_iota_reduction] found recursor: {:?}", rec_name);

        // Calculate total expected args before major premise
        // Standard: params + motives + minors + indices
        // recOn:    params + motives + indices (major before minors)
        let args_before_major = match rec_val.arg_order {
            RecursorArgOrder::MajorAfterMinors => {
                rec_val.num_params as usize
                    + rec_val.num_motives as usize
                    + rec_val.num_minors as usize
                    + rec_val.num_indices as usize
            }
            RecursorArgOrder::MajorAfterMotive => {
                rec_val.num_params as usize
                    + rec_val.num_motives as usize
                    + rec_val.num_indices as usize
            }
        };

        // Need at least enough args to have the major premise (and minors when major precedes them)
        let required_args = match rec_val.arg_order {
            RecursorArgOrder::MajorAfterMinors => args_before_major + 1,
            RecursorArgOrder::MajorAfterMotive => {
                args_before_major + 1 + rec_val.num_minors as usize
            }
        };
        if args.len() < required_args {
            return None;
        }

        // Get the major premise (the value being eliminated)
        let major_arg = args[args_before_major];

        #[cfg(feature = "debug-whnf")]
        eprintln!(
            "[try_iota_reduction] major premise (pre-whnf): {:?}",
            major_arg
        );

        // Lean 4 applies K-conversion before normalizing the major premise
        // (inductive.h:88-91). We mirror that ordering here.
        //
        // Fallback note: clean's try_infer_type_quick cannot infer every expression
        // form (e.g., Let), so we keep a guarded post-whnf K attempt below when this
        // pre-whnf conversion doesn't fire.
        let mut major = major_arg.clone();
        let mut k_reduced_pre_whnf = false;
        if rec_val.is_k {
            #[cfg(feature = "debug-whnf")]
            eprintln!("[try_iota_reduction] is_k=true, trying K reduction before whnf");
            if let Some(k_major) = self.try_to_cnstr_when_k(rec_val, &major, rec_levels) {
                major = k_major;
                k_reduced_pre_whnf = true;
            }
        }

        // Normalize major premise to find constructor head.
        // Lean 4 `inductive_reduce_rec` (inductive.h:91) uses the whnf callback from
        // `reduce_recursor` (type_checker.cpp:340):
        //   cheap_rec ? whnf_core(e, cheap_rec, cheap_proj) : whnf(e)
        // With cheap_rec=false (all current clean modes), this is full whnf. See #1484.
        let major_whnf = if use_delta {
            self.whnf_impl(&major)
        } else {
            self.whnf_core_no_delta(&major, true)
        };

        #[cfg(feature = "debug-whnf")]
        eprintln!(
            "[try_iota_reduction] major premise (post-whnf): {:?}",
            major_whnf
        );

        // Expand literals to constructor form for iota reduction (#574).
        // Per Lean 4: nat_lit_to_constructor, string_lit_to_constructor.
        // This allows Nat.rec to reduce on numeric literals like 3.
        let major_whnf: Expr = match &major_whnf.kind {
            ExprKind::Lit(Literal::Nat(n)) => {
                // GRIND TRACE: this is the recursor-over-large-literal iota step
                // that drives the carrier-tower grind. Logs the enclosing def-eq
                // pair once per frame (gated on CLEAN_TRACE_GRIND; no-op else).
                #[cfg(feature = "reduction-stats")]
                crate::tc::reduction_stats::record_iota_grind(rec_name, n, e);
                nat::nat_lit_to_constructor(n)
            }
            ExprKind::Lit(Literal::String(s)) => {
                let expanded = string_lit_to_constructor(s);
                if use_delta {
                    self.whnf_impl(&expanded)
                } else {
                    self.whnf_core_no_delta(&expanded, true)
                }
            }
            _ => major_whnf,
        };

        // Try structure eta expansion for structure-like inductives (#573).
        // Per Lean 4 inductive.h:60-73 `to_cnstr_when_structure`, which keys on
        // `rec_val.get_major_induct()` — the inductive of the MAJOR premise.
        // For ordinary recursors that equals `inductive_name`, but for the aux
        // recursors of nested inductives (`Trie.rec_3` eliminating `Prod _ _`)
        // `inductive_name` is the family head and struct-eta would never fire,
        // leaving e.g. `Trie.rec_3 … h` stuck where Lean reduces it — the
        // `_sizeOf_N_eq` / `ctor.sizeOf_spec` lemmas of every structure-nested
        // inductive depend on this. Falls back to `inductive_name` if the
        // recursor type is malformed (strictly the pre-existing behavior).
        // SOUNDNESS: completeness-only — eta still requires the major's whnf'd
        // type head to match, structure-likeness, and a rule keyed on that
        // structure's constructor.
        let major_induct = rec_val
            .major_induct()
            .unwrap_or(&rec_val.inductive_name)
            .clone();
        let major_whnf = if let Some(expanded) = self.try_eta_struct(&major_induct, &major_whnf) {
            expanded
        } else {
            major_whnf
        };

        // Post-whnf fallback: if pre-whnf K conversion did not trigger, try once more.
        // This preserves prior behavior for expression forms not handled by
        // try_infer_type_quick before whnf normalization.
        let major_whnf = if rec_val.is_k && !k_reduced_pre_whnf {
            self.try_to_cnstr_when_k(rec_val, &major_whnf, rec_levels)
                .unwrap_or(major_whnf)
        } else {
            major_whnf
        };

        // === HIT path-constructor iota (Cubical mode) ===
        //
        // When the major premise is a *path application* `c @ r` whose path head
        // `c` is a HIT path constructor (its declared type returns a
        // `CubicalPath`, e.g. S¹'s `loop`), the recursor reduces as
        //   `I.rec C minors… (c @ r) ↝ (minor_c applied to C, minors, fields) @ r`.
        // We detect that here, remember the interval argument `r`
        // (`hit_path_arg`), and replace the major premise with `c`'s
        // (whnf'd) constructor application so the standard rule-selection /
        // field-extraction machinery below proceeds unchanged; the `@ r` is
        // re-applied to the computed result just before any extra arguments.
        //
        // SOUNDNESS: this fires only for a genuine path constructor (guarded by
        // the constructor's declared `CubicalPath` return type). The later
        // by-name rule lookup still requires a matching rule in THIS recursor, so
        // a path constructor of an unrelated inductive (or a non-path constructor
        // spuriously applied with `@`) finds no rule and stays stuck. The rewrite
        // is type-preserving: `c @ r : ty r` and `minor_c @ r : ty r` for the
        // same line `ty`, and is endpoint-coherent (`r = i0/i1` reduces both the
        // point rule and `minor_c @ r` to the same minor — see S¹ boundary).
        let mut hit_path_arg: Option<Expr> = None;
        let major_whnf = if let ExprKind::CubicalPathApp { path, arg } = major_whnf.kind() {
            let path_whnf = if use_delta {
                self.whnf_impl(path)
            } else {
                self.whnf_core_no_delta(path, true)
            };
            let is_path_ctor = if let ExprKind::Const(maybe_ctor, _) = path_whnf.get_app_fn().kind()
            {
                self.env.get_constructor(maybe_ctor).is_some_and(|cv| {
                    matches!(
                        get_return_type(&cv.type_).kind(),
                        ExprKind::CubicalPath { .. }
                    )
                })
            } else {
                false
            };
            if is_path_ctor {
                hit_path_arg = Some(arg.as_ref().clone());
                path_whnf
            } else if let Some(endpoint) = self.reduce_path_app_endpoint(path, arg) {
                // Neutral path-endpoint major premise: `q @ i0 ↝ left(q)`,
                // `q @ i1 ↝ right(q)`, reading the endpoints off `q`'s `Path ty
                // left right` type. This lets an eliminator whose major is a
                // *neutral* path applied at a literal interval endpoint fire on
                // the (point-constructor) endpoint — e.g. `helix (q @ i0) ↝ helix
                // base ↝ MyZ`, which is exactly what makes `winding`/`encode`
                // (`coe (λ i. helix (q @ i)) i0 i1 (ofNat 0)`) TYPE-CHECK over an
                // abstract loop `q : Ω S¹`.
                //
                // SOUNDNESS: this is the definitional endpoint rule of the path
                // type (`q @ i0 : ty i0` and `left : ty i0`), so the rewrite is
                // type-preserving; we re-WHNF the endpoint so the standard
                // rule-selection / field-extraction below sees its constructor
                // head. Only fires in Cubical mode (the only mode with
                // `CubicalPathApp`) and only on a literal endpoint with a neutral,
                // non-path-constructor head (otherwise `reduce_path_app_endpoint`
                // returns `None` and the recursor stays stuck, which is sound).
                if use_delta {
                    self.whnf_impl(&endpoint)
                } else {
                    self.whnf_core_no_delta(&endpoint, true)
                }
            } else {
                major_whnf
            }
        } else {
            major_whnf
        };

        // === Recursor-over-hcomp iota (the sound HIT-recursor Kan rule, Cubical) ===
        //
        // When the major premise WHNFs to a `CubicalHComp { ty, phi, u, base }`, a
        // recursor with a *non-dependent* (constant) motive `C ≡ λ_.K` pushes
        // through the composition:
        //
        //   I.rec params motives minors indices (hcomp {I} [φ ↦ u] base)
        //     ↝ hcomp {K} [φ ↦ (rebuild u with each branch λ j. recf (head j))]
        //              (recf base)
        //
        // where `recf = I.rec params motives minors indices` (everything strictly
        // before the major premise). The faces `φ` are reused verbatim.
        //
        // SOUNDNESS: for a *constant* motive `K` the eliminator's action on the
        // inductive's `hcomp` is `hcomp` in the constant `K` — there is NO
        // correction term (the correction in the *dependent* case comes from the
        // motive varying along the composite, which does not happen for a constant
        // `K`). So the rewrite is EXACT and type-preserving (each rebuilt tube
        // `λ j. recf (head j) : I → K` and `recf base : K`). It is boundary
        // coherent: on a true face `φᵢ ⇓ ⊤` the on-a-face hcomp rule reads
        // `headᵢ i1`, so the pushed result reduces to `(λ j. recf (headᵢ j)) i1 =
        // recf (headᵢ i1)` — exactly the recursor applied to the on-a-face value.
        //
        // GUARDS (else stuck): Cubical mode, `MajorAfterMinors`, `num_motives == 1`,
        // no extra args after the major, a literal `λ_.K` motive with `K`
        // argument-independent, and an inferable `K : Sort ℓ`. A dependent motive /
        // recOn / multi-motive / unparseable shape leaves the recursor stuck
        // (returns `None`), which is sound.
        if let ExprKind::CubicalHComp { phi, u, base, .. } = major_whnf.kind() {
            return self.try_recursor_over_hcomp(
                head,
                rec_val,
                &args,
                args_before_major,
                phi,
                u,
                base,
                use_delta,
            );
        }

        // Check if major is a constructor application
        let major_head = major_whnf.get_app_fn().clone();

        #[cfg(feature = "debug-whnf")]
        eprintln!("[try_iota_reduction] major head: {:?}", major_head);

        let ExprKind::Const(ctor_name, _) = &major_head.kind else {
            #[cfg(feature = "debug-whnf")]
            eprintln!("[try_iota_reduction] major head is not Const, returning None");
            return None;
        };

        // Check this is actually a constructor of the inductive
        let ctor_val = self.env.get_constructor(ctor_name)?;

        #[cfg(feature = "debug-whnf")]
        eprintln!(
            "[try_iota_reduction] found constructor: {:?} for inductive {:?}",
            ctor_name, ctor_val.inductive_name
        );

        // === Lean 4-faithful rule selection (kernel/inductive.cpp `get_rec_rule_for`) ===
        //
        // Lean's kernel selects the recursor rule purely by *constructor name*: it
        // scans `rec_val.get_rules()` for the rule whose `m_cnstr` equals the major
        // premise's constructor head. It does NOT compare the constructor's parent
        // inductive against the recursor's inductive. That name match is the entire
        // safety check — if no rule names this constructor, reduction is stuck.
        //
        // The common case (a recursor for inductive `I` applied to a constructor of
        // `I`) is handled by the O(1) index fast path: rules are built in
        // constructor order, so `constructor_idx` indexes the matching rule directly.
        // The fast path still VERIFIES the indexed rule names this constructor:
        // with name-shadowed twin inductives (e.g. Clean's seeded `UInt32` whose
        // sole ctor is `UInt32.mk`, next to an imported genuine `UInt32.ofBitVec`
        // constructor that also claims parent `UInt32`), `constructor_idx` is
        // relative to the OTHER copy's constructor list — trusting it blindly
        // would apply a DIFFERENT constructor's rule (a wrong reduction; formerly
        // only a `debug_assert`, so release builds could mis-reduce). A name
        // mismatch falls through to the by-name scan below.
        //
        // The fast path is also INVALID for nested-inductive auxiliary recursors
        // such as `Lean.Syntax.rec_1`, whose sole rule is for `Array.mk`. There the
        // recursor's `inductive_name` (`Lean.Syntax.rec_1`) differs from the
        // constructor's parent (`Array`), and `Array.mk`'s `constructor_idx` is
        // relative to `Array`, not to the recursor's rule list. For these we fall
        // back to a by-name scan, exactly mirroring Lean's `get_rec_rule_for`.
        //
        // SOUNDNESS: constructor names are fully qualified and globally unique, so a
        // by-name match can only fire on the genuine constructor the rule was built
        // for. An ill-typed application of a recursor to an unrelated constructor
        // finds no matching rule and stays stuck (reduction returns `None`), so the
        // type checker still rejects it. We never widen what reduces — we only stop
        // rejecting the nested-aux case that Lean already reduces.
        let idx_rule = if ctor_val.inductive_name == rec_val.inductive_name {
            rec_val
                .rules
                .get(ctor_val.constructor_idx as usize)
                .filter(|rule| &rule.constructor_name == ctor_name)
        } else {
            None
        };
        let rule = match idx_rule {
            Some(rule) => rule,
            // Nested-aux, twin-skewed, or otherwise non-aligned recursor: locate
            // the rule by constructor name, as Lean's kernel does. No match ⇒
            // stuck.
            None => match rec_val
                .rules
                .iter()
                .find(|r| &r.constructor_name == ctor_name)
            {
                Some(rule) => rule,
                None => {
                    #[cfg(feature = "debug-whnf")]
                    eprintln!(
                        "[try_iota_reduction] no rule for ctor {:?} in recursor {:?}",
                        ctor_name, rec_name
                    );
                    return None;
                }
            },
        };

        // Extract constructor fields using Lean 4's approach (inductive.h:110):
        // nparams = major_args.size() - rule.num_fields
        // This handles the constructor/recursor parameter count asymmetry that
        // occurs with Eq (where init_eq promotes `a` from index to rec-parameter,
        // making rec num_params=2 but ctor num_params=1).
        let major_args = major_whnf.get_app_args();
        let num_major_args = major_args.len();
        if (rule.num_fields as usize) > num_major_args {
            return None;
        }
        let nparams = num_major_args - rule.num_fields as usize;

        // Verify level param count matches (Lean 4 inductive.h:103)
        if rec_levels.len() != rec_val.level_params.len() {
            return None;
        }

        // Determine minor premise location
        let minors_start = match rec_val.arg_order {
            RecursorArgOrder::MajorAfterMinors => {
                rec_val.num_params as usize + rec_val.num_motives as usize
            }
            RecursorArgOrder::MajorAfterMotive => args_before_major + 1,
        };

        // Constructor fields are major_args[nparams..nparams+num_fields].
        // We apply them directly from the slice to avoid an intermediate Vec allocation
        // and an extra round of Arc refcount increments.
        let fields_start = nparams;
        let fields_end = nparams + rule.num_fields as usize;

        // === Lean 4 RHS-based reduction (inductive.h:104-117) ===
        //
        // If the RHS is a lambda term (Lean 4 format, or clean internally-built with
        // lambda wrappers), use the standard approach: instantiate level params, then
        // apply params+motives+minors, then fields.
        //
        // For legacy non-lambda RHS (e.g., noConfusionType placeholder), fall back to
        // the minor+fields manual approach.
        let mut result = if rule.rhs.is_lam() {
            // Step 1: Instantiate universe level parameters in the RHS lambda.
            // The RHS is: λ params. λ motives. λ minors. λ fields. body
            // where body = minor_i fields... IH₀... IHₘ
            let mut result = rule
                .rhs
                .instantiate_level_params_direct(&rec_val.level_params, rec_levels);

            // Step 2: Apply params + motives + minors from recursor application args.
            let n_pm = rec_val.num_params as usize + rec_val.num_motives as usize;
            let n_pmm = n_pm + rec_val.num_minors as usize;

            match rec_val.arg_order {
                RecursorArgOrder::MajorAfterMinors => {
                    for i in 0..n_pmm {
                        result = Expr::app(result, (*args.get(i)?).clone());
                    }
                }
                RecursorArgOrder::MajorAfterMotive => {
                    // Apply params + motives first
                    for i in 0..n_pm {
                        result = Expr::app(result, (*args.get(i)?).clone());
                    }
                    // Minors are after the major premise
                    for j in 0..rec_val.num_minors as usize {
                        let idx = minors_start + j;
                        result = Expr::app(result, (*args.get(idx)?).clone());
                    }
                }
            }

            // Step 3: Apply constructor fields from major premise (inductive.h:112).
            for field in &major_args[fields_start..fields_end] {
                result = Expr::app(result, (*field).clone());
            }

            result
        } else {
            // Legacy fallback for non-lambda RHS (noConfusionType, etc.).
            // Extract minor premise from args and apply fields directly.
            let minor_idx = minors_start + ctor_val.constructor_idx as usize;
            if minor_idx >= args.len() {
                return None;
            }
            let mut result = args[minor_idx].clone();
            for field in &major_args[fields_start..fields_end] {
                result = Expr::app(result, (*field).clone());
            }
            result
        };

        // HIT path-constructor iota: re-apply `@ r` to the computed minor result
        // (`I.rec … (c @ r) ↝ (minor_c …) @ r`) before any extra arguments.
        if let Some(path_arg) = hit_path_arg {
            result = Expr::from_kind(ExprKind::CubicalPathApp {
                path: Arc::new(result),
                arg: Arc::new(path_arg),
            });
        }

        // Apply extra arguments after the major premise (inductive.h:113-117).
        let extras_start = match rec_val.arg_order {
            RecursorArgOrder::MajorAfterMinors => args_before_major + 1,
            RecursorArgOrder::MajorAfterMotive => {
                args_before_major + 1 + rec_val.num_minors as usize
            }
        };
        for extra in &args[extras_start..] {
            result = Expr::app(result, (*extra).clone());
        }

        #[cfg(feature = "debug-whnf")]
        eprintln!("[try_iota_reduction] SUCCESS: result = {:?}", result);
        #[cfg(feature = "reduction-stats")]
        crate::tc::reduction_stats::record_iota_with_witness(rec_name, &result);
        Some(result)
    }

    /// Push an eliminator with a **non-dependent (constant) motive** through a
    /// `hcomp` major premise — the sound HIT-recursor Kan rule. See the call site
    /// in [`Self::try_iota_reduction`] for the rule, soundness argument and guards.
    ///
    /// `head` is the recursor's `Const(I.rec, levels)` spine head; `args` are the
    /// recursor application's arguments (`args_before_major` of them precede the
    /// major premise); `phi`/`u`/`base` are the major `hcomp`'s fields. Returns
    /// `None` (⇒ the recursor stays stuck, which is sound) whenever any guard
    /// fails.
    #[allow(clippy::too_many_arguments)]
    fn try_recursor_over_hcomp(
        &self,
        head: &Expr,
        rec_val: &RecursorVal,
        args: &[&Expr],
        args_before_major: usize,
        phi: &Expr,
        u: &Expr,
        base: &Expr,
        use_delta: bool,
    ) -> Option<Expr> {
        // GUARD: cubical layer only (Cubical, or Directed via the 2LTT bridge).
        if !self.mode.has_cubical_layer() {
            return None;
        }
        // GUARD: standard recursor layout, a single motive, and no extra arguments
        // after the major premise (a dependent eliminator with the major last).
        if rec_val.arg_order != RecursorArgOrder::MajorAfterMinors {
            return None;
        }
        if rec_val.num_motives != 1 {
            return None;
        }
        if args.len() != args_before_major + 1 {
            return None;
        }

        // `recf = I.rec params motives minors indices` — everything strictly before
        // the major premise; `recf v : K` for any major `v : I`.
        let recf = Expr::apps(
            head.clone(),
            args[..args_before_major].iter().map(|a| (*a).clone()),
        );

        // The single motive `C` is the first argument after the parameters.
        let motive = *args.get(rec_val.num_params as usize)?;
        let motive_whnf = if use_delta {
            self.whnf_impl(motive)
        } else {
            self.whnf_core_no_delta(motive, true)
        };
        // GUARD: the motive must be a literal `λ _. K` whose body `K` does not use
        // the eliminated value (a genuinely *non-dependent* / constant motive).
        let ExprKind::Lam(_, _dom, c_body) = motive_whnf.kind() else {
            return None;
        };
        if c_body.has_loose_bvar(0) {
            return None;
        }
        // `K`, lowered out of the (now dead) motive binder. The body carries no
        // loose `BVar(0)`, so `instantiate` merely strips the binder.
        let k = c_body.instantiate(&Expr::from_kind(ExprKind::CubicalI0));

        // Infer the motive universe `K : Sort ℓ` (the level the rebuilt `System`
        // encoding and tube functions must carry). `None` ⇒ stuck.
        let k_sort = self.infer_type_infer_only(&k).ok()?;
        let k_sort_whnf = self.whnf_impl(&k_sort);
        let ExprKind::Sort(level) = k_sort_whnf.kind() else {
            return None;
        };
        let level = level.clone();

        // Rebuild the partial-element system at `K`: every tube head
        // `headᵢ : I → I` becomes `λ j. recf (headᵢ j) : I → K`; the faces are
        // reused verbatim.
        let rebuilt = self.rebuild_recursor_hcomp_system(u, &recf, &k, &level, use_delta)?;

        // Result: `hcomp {K} [φ ↦ rebuilt] (recf base)`. `phi` is reused verbatim.
        Some(Expr::from_kind(ExprKind::CubicalHComp {
            ty: Arc::new(k),
            phi: Arc::new(phi.clone()),
            u: Arc::new(rebuilt),
            base: Arc::new(Expr::app(recf, base.clone())),
        }))
    }

    /// Rebuild a partial-element `System` encoding for the recursor-over-hcomp rule:
    /// re-annotate the `System.cons`/`System.nil` heads at the motive type `K`
    /// (universe `level`) and replace each tube head `headᵢ : I → I` with
    /// `λ j. recf (headᵢ j) : I → K`. The cell faces `φᵢ` are reused verbatim.
    ///
    /// Handles the multi-branch encoding (`System.cons … System.nil`) and the
    /// legacy single-branch bare function `u : I → I` (mapped to `λ j. recf (u j)`).
    /// `head`/`recf`/`level` carry no loose BVars at WHNF time (outer binders are
    /// already opened to FVars), so wrapping them under the fresh `λ j` needs no
    /// index shifting.
    fn rebuild_recursor_hcomp_system(
        &self,
        u: &Expr,
        recf: &Expr,
        k: &Expr,
        level: &Level,
        use_delta: bool,
    ) -> Option<Expr> {
        let interval = || Expr::from_kind(ExprKind::CubicalInterval);
        let w = if use_delta {
            self.whnf_impl(u)
        } else {
            self.whnf_core_no_delta(u, true)
        };
        if let ExprKind::Const(name, _) = w.get_app_fn().kind() {
            let cargs = w.get_app_args();
            if *name == *kan::kan_names::SYSTEM_CONS && cargs.len() == 4 {
                // cargs = [A, φ, head, tail]. Rebuild head as `λ j. recf (head j)`,
                // keep the face `φ` verbatim, recurse on the tail, re-annotate at K.
                let new_head = Expr::lam(
                    BinderInfo::Default,
                    interval(),
                    Expr::app(recf.clone(), Expr::app(cargs[2].clone(), Expr::bvar(0))),
                );
                let new_tail =
                    self.rebuild_recursor_hcomp_system(cargs[3], recf, k, level, use_delta)?;
                return Some(Expr::apps(
                    Expr::const_(kan::kan_names::SYSTEM_CONS.clone(), vec![level.clone()]),
                    [k.clone(), cargs[1].clone(), new_head, new_tail],
                ));
            }
            if *name == *kan::kan_names::SYSTEM_NIL {
                return Some(Expr::app(
                    Expr::const_(kan::kan_names::SYSTEM_NIL.clone(), vec![level.clone()]),
                    k.clone(),
                ));
            }
        }
        // Legacy single-branch bare function `u : I → I` ⇒ `λ j. recf (u j)`.
        Some(Expr::lam(
            BinderInfo::Default,
            interval(),
            Expr::app(recf.clone(), Expr::app(w, Expr::bvar(0))),
        ))
    }

    /// Try to reduce a quotient application (Quot.lift or Quot.ind)
    ///
    /// Reduction rules:
    /// - `Quot.lift.{u v} α r β f h (Quot.mk.{u} α r a) ≡ f a`
    /// - `Quot.ind.{u} α r β f (Quot.mk.{u} α r a) ≡ f a`
    ///
    /// Reference: Lean 4 type_checker.cpp:335 `quot_reduce_rec`
    pub(super) fn try_quot_reduction(&self, e: &Expr, use_delta: bool) -> Option<Expr> {
        // Early exit: check if head is Quot.lift or Quot.ind before collecting args (O(1) vs O(n))
        // This is critical for performance on stuck application chains (#949)
        let head = e.get_app_fn();

        // Quick check: head must be Const(Quot.lift|Quot.ind, _) for quot reduction
        // Exit early to avoid O(n) arg collection on stuck app chains
        let is_lift = matches!(&head.kind, ExprKind::Const(name, _) if *name == *crate::quot::names::QUOT_LIFT);
        let is_ind = matches!(&head.kind, ExprKind::Const(name, _) if *name == *crate::quot::names::QUOT_IND);
        if !is_lift && !is_ind {
            return None;
        }

        // Now collect args (only after confirming head is Quot.lift or Quot.ind)
        let args = e.get_app_args();

        // Use the quot module's reduction functions.
        // Lean 4's quot_reduce_rec (type_checker.cpp:335) always uses full whnf,
        // regardless of cheap_rec. See #1484.
        if is_lift {
            if use_delta {
                crate::quot::try_quot_lift_reduction(head, &args, |expr| self.whnf_impl(expr))
            } else {
                crate::quot::try_quot_lift_reduction(head, &args, |expr| {
                    self.whnf_core_no_delta(expr, true)
                })
            }
        } else {
            // is_ind
            if use_delta {
                crate::quot::try_quot_ind_reduction(head, &args, |expr| self.whnf_impl(expr))
            } else {
                crate::quot::try_quot_ind_reduction(head, &args, |expr| {
                    self.whnf_core_no_delta(expr, true)
                })
            }
        }
    }

    /// Try K-axiom reduction: convert `e : I params indices` to the unique constructor
    /// when the inductive type supports K and all indices are definitionally equal.
    ///
    /// For types like Eq with K-axiom support, this converts any proof `h : a = a`
    /// to `Eq.refl a`, enabling computational behavior for equality proofs.
    ///
    /// Reference: Lean 4 inductive.h:31-49 `to_cnstr_when_K`
    ///
    /// # Arguments
    /// * `rec_val` - The recursor value (must have `is_k == true`)
    /// * `e` - The major premise expression to potentially convert
    /// * `rec_levels` - Universe levels from the recursor application
    ///
    /// # Returns
    /// * `Some(ctor_app)` - The K-like constructor application (with params and unified index) if K reduction applies
    /// * `None` - If K reduction does not apply
    fn try_to_cnstr_when_k(
        &self,
        rec_val: &RecursorVal,
        e: &Expr,
        rec_levels: &[Level],
    ) -> Option<Expr> {
        // Already a constructor - no conversion needed
        if self.is_constructor_app(e) {
            return None;
        }

        // Infer the type of e: should be `I params indices`
        // Lean 4 reference: inductive.h:35 uses full `infer_type(e)`.
        // Using try_infer_type_quick here misses expressions that require
        // full inference (e.g., Let bindings, complex App chains), causing
        // K-reduction to silently fail. Fall back to full infer_type_infer_only
        // when quick inference fails. Part of #3228.
        let e_type = self
            .try_infer_type_quick(e)
            .or_else(|| self.infer_type_infer_only(e).ok())?;
        let e_type_whnf = self.whnf_impl(&e_type);

        // Verify the type head is the expected inductive
        let type_head = e_type_whnf.get_app_fn();
        let ExprKind::Const(type_name, type_levels) = &type_head.kind else {
            return None;
        };
        if type_name != &rec_val.inductive_name {
            return None;
        }

        // Check for metavariables in indices (per Lean 4: skip if has_expr_mvar)
        // clean doesn't have metavariables in the kernel, so skip this check

        // Get the type arguments
        let type_args = e_type_whnf.get_app_args();
        let num_params = rec_val.num_params as usize;

        // K-like types have a single nullary constructor
        // Build the constructor application: ctor params
        if rec_val.rules.len() != 1 {
            return None;
        }
        let ctor_name = &rec_val.rules[0].constructor_name;
        let ctor_val = self.env.get_constructor(ctor_name)?;
        let ctor_arity =
            (ctor_val.num_params as usize).checked_add(ctor_val.num_fields as usize)?;

        // Get constructor levels from recursor levels
        // rec_levels = [motive_level, ind_level_0, ind_level_1, ...]
        // ctor uses ind_levels
        let ctor_levels: LevelVec = if rec_levels.len() > 1 {
            rec_levels[1..].iter().cloned().collect()
        } else {
            type_levels.iter().cloned().collect()
        };

        // Build ctor application: apply params, then any extra args.
        // With fixed_indices_to_params now running in add_inductive, num_params
        // includes promoted indices. Extra ctor args beyond num_params are
        // supplied from the type's index arguments.
        if num_params > ctor_arity || type_args.len() < num_params {
            return None;
        }
        let mut ctor_app = Expr::const_(ctor_name.clone(), ctor_levels);
        for i in 0..num_params {
            ctor_app = Expr::app(ctor_app, type_args[i].clone());
        }

        // Apply extra constructor args (fixed-index promotion case).
        // Each extra arg corresponds to an index from the type arguments.
        let extra_ctor_args = ctor_arity - num_params;
        if type_args.len() < num_params + extra_ctor_args {
            return None;
        }
        for i in 0..extra_ctor_args {
            ctor_app = Expr::app(ctor_app, type_args[num_params + i].clone());
        }

        // Verify the constructed term has the same type as e
        // This checks that indices are definitionally equal.
        // Use full inference with fallback for same reasons as above. Part of #3228.
        let ctor_type = self
            .try_infer_type_quick(&ctor_app)
            .or_else(|| self.infer_type_infer_only(&ctor_app).ok())?;
        if !self.is_def_eq_impl(&e_type_whnf, &ctor_type) {
            return None;
        }

        Some(ctor_app)
    }
}

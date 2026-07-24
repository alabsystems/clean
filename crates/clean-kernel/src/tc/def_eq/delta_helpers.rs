// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::env::TransparencyMode;
use crate::expr::{Expr, ExprKind, LevelVec};
use crate::name::Name;
use crate::tc::reduction::string_lit_to_constructor;
use crate::tc::TypeChecker;
use std::sync::LazyLock;

/// Well-known names for Lean.reduceBool / Lean.reduceNat kernel extensions.
///
/// Reference: Lean 4 type_checker.cpp:1214-1215
///   `g_lean_reduce_bool = new_persistent_expr_const({"Lean", "reduceBool"});`
///   `g_lean_reduce_nat  = new_persistent_expr_const({"Lean", "reduceNat"});`
static LEAN_REDUCE_BOOL: LazyLock<Name> = LazyLock::new(|| Name::from_string("Lean.reduceBool"));
static LEAN_REDUCE_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Lean.reduceNat"));

/// `decide` / `Decidable.decide` — the registered native reducers inspect an
/// instance argument for `Decidable.isTrue` / `Decidable.isFalse` head. In
/// practice the instance is still an unreduced `@inst... a b` application
/// (e.g. a derived `DecidableEq` application from `deriving DecidableEq`).
/// We pre-WHNF the instance at the `reduce_native` callsite so the reducer
/// can fire. Part of #3432.
static DECIDE_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("decide"));
static DECIDABLE_DECIDE_NAME: LazyLock<Name> =
    LazyLock::new(|| Name::from_string("Decidable.decide"));

/// The `UInt*/USize . decEq / decLt` native reducer names whose operands need a
/// pre-WHNF pass (they only recognise the canonical `<T>.mk n` constructor form,
/// but real proof terms supply `OfNat.ofNat`-style literals). See the callsite
/// in `reduce_native` for the soundness argument (WHNF is sound; non-`.mk`
/// operands make the reducer decline → δι fallback).
static WRAPPER_CMP_OPERAND_WHNF: LazyLock<[Name; 10]> = LazyLock::new(|| {
    [
        Name::from_string("UInt8.decEq"),
        Name::from_string("UInt16.decEq"),
        Name::from_string("UInt32.decEq"),
        Name::from_string("UInt64.decEq"),
        Name::from_string("USize.decEq"),
        Name::from_string("UInt8.decLt"),
        Name::from_string("UInt16.decLt"),
        Name::from_string("UInt32.decLt"),
        Name::from_string("UInt64.decLt"),
        Name::from_string("USize.decLt"),
    ]
});

fn wrapper_cmp_needs_operand_whnf(name: &Name) -> bool {
    WRAPPER_CMP_OPERAND_WHNF.iter().any(|n| n == name)
}

impl<'env> TypeChecker<'env> {
    pub(in crate::tc::def_eq) fn try_unfold_const_in_place(
        &self,
        expr: &mut Expr,
        name: &Name,
        levels: &LevelVec,
        _mode: TransparencyMode,
    ) -> bool {
        // B14 elaboration-time reducibility gate. When the opt-in
        // `honor_reducibility` flag is on (elaborator/unifier) and the active
        // transparency is not `All`, an `@[irreducible]` definition does NOT
        // delta-unfold — matching MetaM `canUnfold` at `.default`. This is the
        // strictly-narrowing direction: it can only turn a former def-eq accept
        // into a reject. Off by default → the trusted kernel path unfolds
        // everything (transparency-blind, Lean-faithful), unchanged.
        //
        // NOTE: `get_delta_const` already excludes theorems (`Opaque` hint), so
        // only `Reducible`/`Regular`/`Irreducible` heads reach here; gating on
        // `Irreducible` leaves `Regular`/`@[reducible]` unfolding intact.
        if self.reducibility_gate_blocks(name) {
            return false;
        }
        // Use cached unfold_definition (not unfold_with_transparency) to match
        // Lean 4's kernel behavior: the kernel type checker has no transparency
        // modes and unfolds any definition or theorem. Only opaque declarations
        // are blocked. Caching matches Lean 4's m_unfold (type_checker.h:31).
        // Reference: Lean 4 type_checker.cpp:884 lazy_delta_reduction_step calls
        // unfold_definition which has no transparency check.
        // Part of #3210.
        // `levels.clone()` keeps the `LevelVec` (SmallVec) inline for the common
        // ≤2-level case; `.to_vec()` would force a heap `Vec` (and stay spilled).
        // Same name + same levels ⇒ identical `Const`, so every verdict is unchanged.
        let const_expr = Expr::const_(name.clone(), levels.clone());
        let Some(value) = self.unfold_definition_cached(&const_expr) else {
            return false;
        };
        let reduced = self.whnf_core_no_delta(&self.replace_head_const(expr, &value), true);
        *expr = reduced;
        true
    }

    pub(in crate::tc::def_eq) fn is_def_eq_args_only(&self, a: &Expr, b: &Expr) -> bool {
        let a_fn = a.get_app_fn();
        let b_fn = b.get_app_fn();
        match (a_fn.kind(), b_fn.kind()) {
            (ExprKind::Const(_, ls1), ExprKind::Const(_, ls2)) => {
                if ls1.len() != ls2.len()
                    || !ls1
                        .iter()
                        .zip(ls2.iter())
                        .all(|(l1, l2)| self.levels_eq(l1, l2))
                {
                    return false;
                }
            }
            _ => return false,
        }

        let mut a_iter = a.get_app_args_iter();
        let mut b_iter = b.get_app_args_iter();
        loop {
            match (a_iter.next(), b_iter.next()) {
                (Some(a_arg), Some(b_arg)) => {
                    if !self.is_def_eq_impl(a_arg, b_arg) {
                        return false;
                    }
                }
                (None, None) => return true,
                _ => return false,
            }
        }
    }

    pub(in crate::tc::def_eq) fn get_delta_const(
        &self,
        e: &Expr,
    ) -> Option<(Name, LevelVec, crate::env::Reducibility)> {
        let head = e.get_app_fn();
        if let ExprKind::Const(name, levels) = head.kind() {
            if let Some(info) = self.env.get_const(name) {
                // Match Lean 4's is_delta (type_checker.cpp:487-494):
                // A constant is delta-reducible if it has a value AND its
                // reducibility hints are not Opaque.
                //
                // In Lean 4, `is_delta` checks `d.get_hints() != ReducibilityHints::Opaque`.
                // Theorems have `ReducibilityHints::Opaque` (declaration.cpp:46),
                // so they do NOT participate in the lazy delta reduction loop.
                // This is critical: Eq.trans/Eq.symm are theorems whose bodies
                // contain Eq.rec applications that cannot reduce when the major
                // premise is an axiom-typed proof. Pulling them into lazy delta
                // causes unbounded unfolding cycles. Part of #3305.
                //
                // Note: Theorems CAN still be unfolded by WHNF (via
                // `whnf_outer_loop` -> `try_unfold_definition` -> `unfold_definition`),
                // which checks `kind != Opaque` (ConstantKind). The distinction is:
                // - WHNF unfolds theorems (correct, needed for iota on Eq.rec)
                // - lazy_delta_reduction does NOT unfold theorems (avoids cycles)
                //
                // Opaque constants (ConstantKind::Opaque) also don't participate.
                // Axioms have value=None so they're excluded by the is_some() check.
                //
                // Level parameter count must match (Lean 4: is_delta line 491).
                // Without this check, get_delta_const could report a constant
                // as delta-reducible while unfold_definition returns None due
                // to level mismatch, causing the fallback logic in
                // lazy_delta_step_both to unfold the wrong side. Part of #3134.
                if info.value.is_some()
                    && info.kind != crate::env::ConstantKind::Opaque
                    && info.reducibility != crate::env::Reducibility::Opaque
                    && levels.len() == info.level_params.len()
                {
                    // PERF-CLASS GUARD (carrier tower): a native Nat op whose
                    // recursion count is a large closed literal is NOT offered as
                    // a lazy-delta candidate — otherwise `try_unfold_const_in_place`
                    // would unfold it (bypassing WHNF's own guard) into a Θ(count)
                    // unary `Nat.rec` grind (e.g. `Nat.sub m 2^31`). Leaving it
                    // stuck keeps def-eq structural, exactly as Lean's kernel does
                    // on these omega/`decide` certificates. Sound: the stuck form
                    // is def-eq to the unfolded form (see
                    // `native_nat_binop_grind_stuck`), so this only ever declines a
                    // provably-redundant unfolding; it never widens def-eq.
                    if self.native_nat_binop_grind_stuck(name, e) {
                        return None;
                    }
                    return Some((name.clone(), levels.clone(), info.reducibility));
                }
            }
        }
        None
    }

    fn replace_head_const(&self, e: &Expr, new_head: &Expr) -> Expr {
        if !e.is_app() {
            return new_head.clone();
        }
        // Flat reconstruction: collect args then rebuild App chain.
        // Avoids O(N) recursive stack depth for N-argument applications.
        // Lean 4 equivalent: mk_rev_app(val, args) in type_checker.cpp.
        // Part of #3210.
        let args = e.get_app_args();
        let mut result = new_head.clone();
        for arg in &args {
            result = Expr::app(result, (*arg).clone());
        }
        result
    }

    pub(in crate::tc::def_eq) fn reduce_proj_core(&self, c: &Expr, idx: u32) -> Option<Expr> {
        let c = match c.kind() {
            ExprKind::Lit(crate::expr::Literal::String(s)) => {
                let expanded = string_lit_to_constructor(s);
                self.whnf_impl(&expanded)
            }
            _ => c.clone(),
        };

        let ExprKind::Const(ctor_name, _) = c.get_app_fn().kind() else {
            return None;
        };
        let ctor_val = self.env.get_constructor(ctor_name)?;
        let args = c.get_app_args();
        let field_idx = (ctor_val.num_params as usize).saturating_add(idx as usize);
        (field_idx < args.len()).then(|| args[field_idx].clone())
    }

    /// Try to reduce a projection-headed application.
    ///
    /// When the head of an application is a `Proj`, attempts reduction via
    /// `whnf_core` with NO head delta but **full** projection reduction
    /// (`cheap_proj = false`).
    ///
    /// Lean 4 parity (type_checker.cpp:868-873): Lean 4 calls
    /// `whnf_core(e)` with the function's **default arguments**
    /// `cheap_rec=false, cheap_proj=false` (type_checker.h:165). With
    /// `cheap_proj=false`, `reduce_proj` runs the *full* `whnf` (including
    /// delta) on the projection's major premise (type_checker.cpp:382-385),
    /// so that `Proj(S, i, e)` whose operand `e` is a delta-reducible
    /// constant/instance application (e.g. a UInt coercion `toBitVec (a *ᵁ b)`
    /// whose definition body is the projection `fun u => u.toBitVec`) reduces
    /// the operand to its constructor form and projects through it. This is
    /// the reconvergence step that lets a coercion-definition over an open
    /// arithmetic operand meet the already-pushed `BitVec` form inside the
    /// lazy-delta loop's asymmetric `*_only` arms.
    ///
    /// Using cheap projection here (`cheap_proj=true`) left such projections
    /// stuck on the open side while the other side kept delta-unfolding, so
    /// the two never reconverged and a genuinely def-eq pair was rejected
    /// (the UInt/BitVec coercion-arithmetic completeness gap, P1 olean
    /// re-verify). Soundness is unchanged: `reduce_proj` only ever extracts a
    /// real field from a genuine constructor application, a sound reduction
    /// Lean's kernel performs identically; it can never equate non-def-eq
    /// terms.
    ///
    /// Part of #3134.
    pub(in crate::tc::def_eq) fn try_unfold_proj_app(&self, e: &Expr) -> Option<Expr> {
        if e.get_app_fn().is_proj() {
            // Lean 4: whnf_core(e) = whnf_core(e, false, false) = NoDeltaFullProj
            let e_new = self.whnf_core_no_delta(e, false);
            if e_new != *e {
                return Some(e_new);
            }
        }
        None
    }

    /// Try to reduce an expression via native reducers or kernel extensions.
    ///
    /// Handles three categories:
    /// 1. **Lean.reduceBool / Lean.reduceNat** — kernel extensions that evaluate a
    ///    zero-argument constant and return its Bool/Nat value. In Lean 4 these use
    ///    the IR interpreter (`ir::run_boxed_kernel`); clean approximates by WHNF-
    ///    reducing the constant's definition value.
    /// 2. **Registered native reducers** — fast-path computation for specific constants
    ///    like `Nat.decEq`, `String.append`, etc.
    ///
    /// Also handles `Lean.reduceBool` and `Lean.reduceNat` — deprecated opaque
    /// constants used for proof-by-reflection. In Lean 4, these JIT-compile and
    /// execute the argument; clean approximates this by WHNF-reducing the
    /// argument constant's value and checking if it reaches a Bool/Nat literal.
    ///
    /// Reference: Lean 4 type_checker.cpp:546-568 `reduce_native`,
    /// Init/Core.lean:2402-2419 `Lean.reduceBool`/`Lean.reduceNat`.
    /// Part of #3210.
    pub(in crate::tc) fn reduce_native(&self, e: &Expr) -> Option<Expr> {
        // Check for Lean.reduceBool / Lean.reduceNat kernel extensions first.
        // Pattern: `App(Const("Lean.reduceBool"), Const(target_name))`
        // In Lean 4, the expression is `Lean.reduceBool someConst` where someConst
        // is a zero-argument function. The kernel evaluates someConst via the IR
        // interpreter and returns Bool.true/false or a Nat literal.
        //
        // Reference: Lean 4 type_checker.cpp:546-567
        if let ExprKind::App(f, arg) = e.kind() {
            if let ExprKind::Const(f_name, _) = f.kind() {
                if *f_name == *LEAN_REDUCE_BOOL {
                    return self.try_reduce_bool(arg);
                }
                if *f_name == *LEAN_REDUCE_NAT {
                    return self.try_reduce_nat_ext(arg);
                }
            }
        }

        let head = e.get_app_fn();
        let ExprKind::Const(name, _) = head.kind() else {
            return None;
        };

        // Look up a native reducer for this constant
        let reducer = self.env.get_native_reducer(name)?;

        // Collect arguments (these are not WHNF'd — the reducer handles that if needed)
        let args = e.get_app_args();

        // Pre-WHNF the instance argument for `decide` / `Decidable.decide`
        // (#3432). `reduce_decide` inspects the head of `args[1]` for
        // `Decidable.isTrue` / `Decidable.isFalse`. When the instance is a
        // derived decEq application like `instColorDecidableEq Color.red
        // Color.red`, the head is not yet a constructor — we have to force
        // reduction so the native reducer can fire. Returning `None` here
        // (if the reducer cannot resolve even after WHNF) falls through to
        // the normal delta path, preserving soundness.
        if (*name == *DECIDE_NAME || *name == *DECIDABLE_DECIDE_NAME) && args.len() >= 2 {
            let inst_whnf = self.whnf_impl(args[1]);
            let mut args_ref: Vec<&Expr> = args.iter().copied().collect();
            args_ref[1] = &inst_whnf;
            return reducer(&args_ref);
        }

        // Pre-WHNF the two operands for the single-constructor `Nat`-wrapper
        // comparison reducers (`UInt*/USize . decEq / decLt`). Those reducers
        // recognise the canonical constructor form `<T>.mk n` (via
        // `get_uint_ctor_val`), but in real proof terms the operands arrive as
        // `@OfNat.ofNat <T> k (<T>.instOfNat k)` (numeric literals) or other
        // δ-reducible aliases. WHNF turns those into `<T>.mk k` so the reducer
        // can fire; if WHNF does NOT reach `<T>.mk`, the reducer still declines
        // and the kernel falls back to ordinary δι reduction of the real
        // definition. WHNF is the kernel's own sound reduction and the operands
        // it produces are def-eq to the originals, so the witness the reducer
        // builds is def-eq to the one over the original operands — sound.
        if wrapper_cmp_needs_operand_whnf(name) && args.len() >= 2 {
            let a_whnf = self.whnf_impl(args[0]);
            let b_whnf = self.whnf_impl(args[1]);
            let mut args_ref: Vec<&Expr> = args.iter().copied().collect();
            args_ref[0] = &a_whnf;
            args_ref[1] = &b_whnf;
            return reducer(&args_ref);
        }

        // NOTE: the BitVec arith/logic/shift/cmp reducers deliberately do NOT
        // get an operand pre-WHNF pass here. Eagerly WHNF-ing their operands
        // forces the reducer to fire on `UInt*.toBitVec a` projection forms and
        // collapse concrete BitVec subterms to bare `Nat` literals; that
        // rewrites the NORMAL FORM of arithmetic inside real proof terms (e.g.
        // `Char.toLower._proof_1` reassociates `0xD800 - 32 + 32` in a way the
        // olean's declared type does not), desyncing a def-eq the ordinary δι
        // tower reduction closes — a measured regression on
        // `Init.Data.Char.Basic`. Without pre-WHNF the reducers still fire on
        // the canonical BitVec value forms (`BitVec.ofNat/ofNatLT/ofFin`, raw
        // `Nat` literal) that `get_bitvec_operand` peels — the fast O(1) path
        // for genuine BitVec-literal computations — while non-literal operands
        // decline and fall back to δι exactly as before, preserving parity.
        reducer(&args)
    }

    /// Try to evaluate `Lean.reduceBool target` by WHNF-reducing the argument.
    ///
    /// Handles three cases:
    /// 1. Argument is already `Bool.true`/`Bool.false` — return directly
    /// 2. Argument is a Const with a definition — unfold and WHNF
    /// 3. General expression — WHNF and check
    ///
    /// This is a sound approximation of Lean 4's `ir::run_boxed_kernel`: we can only
    /// reduce constants whose value WHNF-reduces to a Bool literal within the heartbeat
    /// budget. Constants that require unbounded computation will fail to reduce (returning
    /// None), which is safe — the caller treats None as "cannot reduce further".
    ///
    /// Reference: Lean 4 type_checker.cpp:550-557
    fn try_reduce_bool(&self, arg: &Expr) -> Option<Expr> {
        // Fast path: argument is already a Bool constructor
        if let Some(result) = Self::extract_bool_value(arg) {
            return Some(result);
        }
        // Try to unfold if it's a constant, then WHNF
        let to_reduce = if matches!(arg.kind(), ExprKind::Const(_, _)) {
            self.unfold_definition_cached(arg)?
        } else {
            return None;
        };
        let reduced = self.whnf_impl(&to_reduce);
        Self::extract_bool_value(&reduced)
    }

    /// Try to evaluate `Lean.reduceNat target` by WHNF-reducing the argument.
    ///
    /// Handles three cases:
    /// 1. Argument is already a Nat literal — return directly
    /// 2. Argument is a Const with a definition — unfold and WHNF
    /// 3. General expression — WHNF and check
    ///
    /// Reference: Lean 4 type_checker.cpp:558-565
    fn try_reduce_nat_ext(&self, arg: &Expr) -> Option<Expr> {
        // Fast path: argument is already a Nat literal
        if let Some(result) = Self::extract_nat_value(arg) {
            return Some(result);
        }
        // Try to unfold if it's a constant, then WHNF
        let to_reduce = if matches!(arg.kind(), ExprKind::Const(_, _)) {
            self.unfold_definition_cached(arg)?
        } else {
            return None;
        };
        let reduced = self.whnf_impl(&to_reduce);
        Self::extract_nat_value(&reduced)
    }

    /// Extract a Bool value from a WHNF'd expression.
    ///
    /// Returns `Some(Bool.true)` or `Some(Bool.false)` if the expression is a
    /// Bool constructor. Returns None otherwise.
    fn extract_bool_value(e: &Expr) -> Option<Expr> {
        static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
        static BOOL_FALSE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));

        let head = e.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            if *name == *BOOL_TRUE {
                return Some(Expr::const_(BOOL_TRUE.clone(), vec![]));
            }
            if *name == *BOOL_FALSE {
                return Some(Expr::const_(BOOL_FALSE.clone(), vec![]));
            }
        }
        None
    }

    /// Extract a Nat literal from a WHNF'd expression.
    ///
    /// Returns `Some(Expr::nat_lit(n))` if the expression is a Nat literal.
    /// Returns None otherwise.
    fn extract_nat_value(e: &Expr) -> Option<Expr> {
        if let ExprKind::Lit(crate::expr::Literal::Nat(_)) = e.kind() {
            return Some(e.clone());
        }
        // Also check for Nat.zero constructor
        if let ExprKind::Const(name, levels) = e.kind() {
            static NAT_ZERO: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.zero"));
            if levels.is_empty() && *name == *NAT_ZERO {
                return Some(Expr::nat_lit(0));
            }
        }
        None
    }
}

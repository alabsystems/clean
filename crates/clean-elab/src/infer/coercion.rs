// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type coercion and numeric literal elaboration.
//!
//! Extracted from `infer/mod.rs`. Contains methods for type coercion
//! (e.g., Nat → Real via Coe instances) and numeric literal construction
//! (via OfNat instance resolution with hardcoded fallbacks).

use super::*;
use std::collections::{HashSet, VecDeque};

/// True if `e` — already metavar-instantiated — still contains an UNASSIGNED
/// metavariable. Clean represents metavariables as `FVar`s with a `MetaState`-
/// encoded id (`MetaState::to_fvar`); after `instantiate`, any surviving such
/// fvar is unassigned. Used to reject a partially-resolved instance (e.g.
/// `OfNat Int 0` resolves to `Zero.toOfNat0` with an unresolved `[Zero Int]`
/// deferred arg) so numeric-literal elaboration falls through to a ground
/// constructor instead of registering a term with free variables.
fn has_unassigned_meta(e: &Expr) -> bool {
    match e.kind() {
        ExprKind::FVar(id) => MetaState::from_fvar(*id).is_some(),
        ExprKind::App(f, a) => has_unassigned_meta(f) || has_unassigned_meta(a),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            has_unassigned_meta(t) || has_unassigned_meta(b)
        }
        ExprKind::Let(_, t, v, b, _) => {
            has_unassigned_meta(t) || has_unassigned_meta(v) || has_unassigned_meta(b)
        }
        ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => has_unassigned_meta(x),
        _ => false,
    }
}

impl<'a> ElabCtx<'a> {
    /// Elaborate a natural number literal to a kernel Expr::Lit(Nat(n)).
    ///
    /// When an expected type is provided (e.g., UInt8), type coercion will be handled
    /// by `elab_nat_literal_with_expected` which tries OfNat instance resolution
    /// first, then falls back to hardcoded constructors.
    pub(in crate::infer) fn elab_nat_literal(&mut self, n: &BigNat) -> Result<Expr, ElabError> {
        Ok(Expr::bignat_lit(n.clone()))
    }

    /// Elaborate a character literal `'a'` to its canonical kernel form
    /// `Char.ofNat <codepoint>`.
    ///
    /// `Char` is a concrete prelude type whose values are built from the
    /// Unicode scalar value via `Char.ofNat`; Lean 4 elaborates char literals
    /// the same way. The numeric argument is the `char`'s scalar value, which
    /// always fits in a `u32` (and hence the kernel `Nat` literal).
    pub(in crate::infer) fn elab_char_literal(&mut self, c: char) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Char.ofNat"), vec![]),
            Expr::nat_lit(u64::from(u32::from(c))),
        )
    }

    /// Elaborate a natural number literal with an expected type.
    ///
    /// Resolution order:
    /// 1. Try OfNat instance resolution: look up `OfNat <expected_ty> <n>` and
    ///    project via `OfNat.ofNat` if found. This handles user-defined OfNat
    ///    instances and polymorphic numeric literals (`(3 : α)` where α has
    ///    `OfNat α 3`).
    /// 2. Fall back to hardcoded constructors for built-in types (Int, UInt8,
    ///    UInt16, UInt32, UInt64, USize) so elaboration still works when the
    ///    environment lacks OfNat instances (e.g., minimal .olean imports).
    /// 3. Default: return raw Nat literal.
    ///
    /// For example, `1 : Int` becomes `Int.ofNat 1` and `1 : UInt8` becomes
    /// `UInt8.ofNat 1` (v4.30 `ofBitVec` carrier; the old `UInt8.mk` ctor is
    /// gone — see the fallback block below).
    pub(in crate::infer) fn elab_nat_literal_with_expected(
        &mut self,
        n: &BigNat,
        expected_ty: &Expr,
    ) -> Expr {
        let expected_whnf = self.whnf(expected_ty);

        // Step 0: OPEN-carrier default — Lean's `@[default_instance]` semantics.
        //
        // A numeric literal whose expected type is still an UNASSIGNED
        // metavariable (`(0 : ?α)` — e.g. operand-0 of `0 ≤ v` / `0 = v`,
        // elaborated before the sibling operand pins the shared carrier) is,
        // in real Lean, POSTPONED and then resolved by the default-instance
        // mechanism: Lean core's only `@[default_instance]` for `OfNat` is
        // `instOfNatNat : OfNat Nat n` (Init/Prelude), so the literal defaults
        // to `Nat` regardless of what else sits in the instance table.
        //
        // Eagerly running the Step-1 search on the open goal `OfNat ?α n`
        // instead commits `?α` to the carrier of whichever candidate sits
        // first in table order — a value the ORDERING, not the program,
        // chooses. Before sweep B12 the first-registered instance won, which
        // happened to be `instOfNatNat` (Lean's outcome, by registration-order
        // luck); B12's Lean-faithful most-recent-first tier order (kernel
        // `register_instance` prepend) flipped that accidental winner to the
        // LAST-registered carrier — `instOfNatFloat` under the imported
        // Lean-core `Init` closure (Float imports late) — so `(h0 : 0 ≤ v)`
        // with `v : Int` pinned `?α := Float` and died with "const mismatch:
        // Int vs Float" (both trust-ir bridge-prelude decls; trust-clean
        // `bridge_gate_default_on` PreludeFailed).
        //
        // Pin the open carrier to `Nat` exactly as Lean's default instance
        // would, then continue into the ordinary — now ground — Step-1 search
        // (which any tier order resolves to `instOfNatNat`). Determined goals
        // never reach this arm, so B12's most-recent-first semantics for real
        // instance selection (its p06 value pins) are untouched, and the
        // downstream operand-driven repair lanes (`elab_app_with_int_coercion`
        // — "operand-0 of `0 ≤ a`" — and the Real retry) behave exactly as on
        // the pre-B12 pin. Regression pin: tests/ofnat_open_carrier_default.rs.
        //
        // B99: the `@[default_instance]` TABLE drives this defaulting in real
        // Lean — `instOfNatNat` is merely its 1000-priority entry. When the
        // file registered its own `OfNat` default instance at priority >=
        // 1000 (e.g. `@[default_instance 2000] instance : OfNat MyType n`),
        // that entry outranks `instOfNatNat`, so consult the table BEFORE the
        // hard Nat pin: the stuck-goal defaulting in `resolve_instance`
        // assigns the carrier from the winning entry. On failure — or when
        // no user default at the `instOfNatNat` tier exists — the Nat pin
        // proceeds exactly as before (files without user `OfNat` default
        // instances take the pre-B99 path byte-for-byte).
        let expected_whnf = if matches!(
            expected_whnf.kind(),
            ExprKind::FVar(id) if MetaState::from_fvar(*id).is_some()
        ) {
            let ofnat = Name::from_string("OfNat");
            let has_user_default_at_nat_tier = self
                .default_instances
                .get(&ofnat)
                .is_some_and(|entries| entries.iter().any(|(_, priority)| *priority >= 1000));
            let defaulted_carrier = has_user_default_at_nat_tier && {
                let ofnat_levels = self
                    .env
                    .get_const(&ofnat)
                    .map(|c| vec![Level::zero(); c.level_params.len()])
                    .unwrap_or_default();
                let goal = Expr::app(
                    Expr::app(Expr::const_(ofnat, ofnat_levels), expected_whnf.clone()),
                    Expr::bignat_lit(n.clone()),
                );
                self.resolve_instance(&goal).is_some()
            };
            if defaulted_carrier {
                // The default instance assigned the carrier metavariable;
                // hand the now-ground carrier to Step 1.
                self.whnf(&self.metas.instantiate(&expected_whnf))
            } else {
                let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
                if self.try_unify(&expected_whnf, &nat_ty) {
                    nat_ty
                } else {
                    expected_whnf
                }
            }
        } else {
            expected_whnf
        };

        // Normalize the expected type's ARGUMENTS, not just its head: `whnf`
        // of the application `Fin (2+3)` is already head-normal and leaves the
        // computed bound untouched, but the registered Fin instance head is
        // succ-shaped (`OfNat (Fin (n+1)) i`), so the Step-1 goal only matches
        // once the bound reduces to a literal (`Fin 5`). A type whose args are
        // already normal is rebuilt identically, so previously-resolving
        // literals are untouched (engagement gate). B95.
        let expected_whnf = {
            let args = expected_whnf.get_app_args();
            if args.is_empty() {
                drop(args);
                expected_whnf
            } else {
                let mut rebuilt = expected_whnf.get_app_fn().clone();
                for arg in &args {
                    rebuilt = Expr::app(rebuilt, self.whnf(arg));
                }
                rebuilt
            }
        };

        // Step 1: Try OfNat instance resolution (#1154).
        // Build the goal type `OfNat <expected_ty> <n>` and resolve it.
        if self.instances.is_class(&Name::from_string("OfNat")) {
            // `OfNat`/`OfNat.ofNat` must be applied with the universe-level count
            // their declarations actually carry: Clean's builtin versions are
            // level-monomorphic (0 params), but the imported Lean
            // `OfNat.{u} : Type u → Nat → Type u` / `OfNat.ofNat.{u}` take 1.
            // Supplying the wrong count is a `LevelCountMismatch` that breaks
            // EVERY numeric literal once a Lean `.olean` is imported. `Level::zero`
            // per param is correct for the Type-0 numeric types (Nat/Int/Fin/UInt).
            let ofnat_levels = self
                .env
                .get_const(&Name::from_string("OfNat"))
                .map(|c| vec![Level::zero(); c.level_params.len()])
                .unwrap_or_default();
            // OfNat takes (α : Type) (n : Nat), so the goal is `OfNat α (natLit n)`.
            let ofnat_goal = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("OfNat"), ofnat_levels),
                    expected_whnf.clone(),
                ),
                Expr::bignat_lit(n.clone()),
            );
            if let Some(inst_expr) = self.resolve_instance(&ofnat_goal) {
                // Instantiate assigned metavars, then REQUIRE the instance be
                // ground: `OfNat α 0`/`OfNat α 1` resolve via the `Zero.toOfNat0`
                // / `One.toOfNat1` bridges, whose `[Zero α]`/`[One α]` deferred
                // arg may be unresolvable (e.g. `Zero Int` absent) — leaving an
                // unassigned metavar. Using such a term builds `@OfNat.ofNat Int 0
                // ?m`, which fails kernel registration with "contains free
                // variables". When non-ground, fall through to the Step-2
                // hardcoded constructor (`Int.ofNat n`), which is always ground.
                let inst_expr = self.metas.instantiate(&inst_expr);
                // Project: `@OfNat.ofNat <expected_ty> <n> <inst_expr>`
                if !has_unassigned_meta(&inst_expr)
                    && self
                        .env
                        .get_const(&Name::from_string("OfNat.ofNat"))
                        .is_some()
                {
                    let ofnat_ofnat_levels = self
                        .env
                        .get_const(&Name::from_string("OfNat.ofNat"))
                        .map(|c| vec![Level::zero(); c.level_params.len()])
                        .unwrap_or_default();
                    return Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(Name::from_string("OfNat.ofNat"), ofnat_ofnat_levels),
                                expected_whnf.clone(),
                            ),
                            Expr::bignat_lit(n.clone()),
                        ),
                        inst_expr,
                    );
                }
            }
        }

        // Step 2: Hardcoded fallback for built-in types when OfNat instances are
        // unavailable (e.g., minimal environments without Init .olean).
        if let ExprKind::Const(name, _) = expected_whnf.kind() {
            let name_str = name.to_string();
            match name_str.as_str() {
                "Int" => {
                    return Expr::app(
                        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                        Expr::bignat_lit(n.clone()),
                    );
                }
                // v4.30 carrier: `UInt*`/`USize` are `ofBitVec`-backed, so the old
                // `<T>.mk : Fin <T>.size → <T>` ctor no longer exists. Emit the
                // shape-stable `<T>.ofNat <lit>` (genuine Lean spelling;
                // `UInt8.ofNat n := UInt8.ofBitVec (BitVec.ofNat 8 n)`), which
                // typechecks under the reshaped carrier and δ-unfolds to the real
                // ctor (design 2026-07-03 §2.3, P0 Q5).
                "UInt8" => {
                    return Expr::app(
                        Expr::const_(Name::from_string("UInt8.ofNat"), vec![]),
                        Expr::bignat_lit(n.clone()),
                    );
                }
                "UInt16" => {
                    return Expr::app(
                        Expr::const_(Name::from_string("UInt16.ofNat"), vec![]),
                        Expr::bignat_lit(n.clone()),
                    );
                }
                "UInt32" => {
                    return Expr::app(
                        Expr::const_(Name::from_string("UInt32.ofNat"), vec![]),
                        Expr::bignat_lit(n.clone()),
                    );
                }
                "UInt64" => {
                    return Expr::app(
                        Expr::const_(Name::from_string("UInt64.ofNat"), vec![]),
                        Expr::bignat_lit(n.clone()),
                    );
                }
                "USize" => {
                    return Expr::app(
                        Expr::const_(Name::from_string("USize.ofNat"), vec![]),
                        Expr::bignat_lit(n.clone()),
                    );
                }
                // `(n : Float)` lowers through `Float.ofNat` (Lean's
                // `instOfNatFloat n := ⟨Float.ofNat n⟩`). Without this arm a
                // bare `Nat` literal ascribed to `Float` fell through to Step 3
                // and elaborated as a raw `Nat`, so `(3.14 : Float) = (3 : Float)`
                // mismatched "expected Float, got Nat" — a Float position holding
                // a Nat. `Float.ofNat : Nat → Float` is a registered kernel const.
                "Float" => {
                    return Expr::app(
                        Expr::const_(Name::from_string("Float.ofNat"), vec![]),
                        Expr::bignat_lit(n.clone()),
                    );
                }
                _ => {}
            }
        }

        // Step 3: Default — return raw Nat literal.
        Expr::bignat_lit(n.clone())
    }

    /// Try to coerce an expression from one type to another.
    ///
    /// Resolution order:
    /// 1. Try Coe instance resolution: look up `Coe <from_ty> <to_ty>` and
    ///    apply via `Coe.coe` if found. This handles user-defined coercion
    ///    instances.
    /// 2. Hardcoded fallback: Nat → Real via `Real.ofNat` when Coe instances
    ///    are unavailable.
    ///
    /// Returns Some(coerced_expr) if coercion succeeded, None otherwise.
    pub(in crate::infer) fn try_coerce(
        &mut self,
        expr: &Expr,
        from_ty: &Expr,
        to_ty: &Expr,
    ) -> Option<Expr> {
        let from_whnf = self.whnf(from_ty);
        let to_whnf = self.whnf(to_ty);

        // Step 1: Try a single-step `Coe` instance resolution (#1154).
        // Build the goal type `Coe <from_ty> <to_ty>` and resolve it.
        if self.instances.is_class(&Name::from_string("Coe"))
            && self.env.get_const(&Name::from_string("Coe.coe")).is_some()
        {
            if let Some(coercion) = self.try_coerce_coe_step(expr, &from_whnf, &to_whnf) {
                return Some(coercion);
            }

            // Step 1b: Multi-step / transitive coercion through `Coe` instances.
            // A bare `Coe A B` + `Coe B C` does not register a direct `Coe A C`
            // instance, so the single-step lookup above misses it. Compose the
            // imported instances along a `from -> … -> to` path: each edge is a
            // `Coe Ti Ti+1` instance and the result is the nested application
            //   `Coe.coe T_{n-1} Tn instN ( … (Coe.coe T0 T1 inst0 expr) … )`.
            // The kernel re-checks the produced term, so a wrong path simply
            // fails to type-check rather than passing silently.
            if let Some(coercion) = self.try_coerce_coe_chain(expr, &from_whnf, &to_whnf) {
                return Some(coercion);
            }
        }

        // Step 1b2: `Subtype α p → α` via `@Subtype.val` (Lean's `instCoeSubtype`
        // / the structure CoeOut `↑x = x.val`). Tried after the `Coe`-instance
        // steps so a genuine imported `Coe` still wins, but always attempted (it
        // is NOT gated on the `Coe` class being set up). The head-name coercion
        // registry cannot express it because the target base `α` is a variable
        // extracted from the subtype's own argument, not a fixed head constant.
        if let Some(coercion) = self.try_coerce_subtype_val(expr, &from_whnf, &to_whnf) {
            return Some(coercion);
        }

        // Step 1b3: Built-in `Nat → Int` widening via `Int.ofNat`. Lean coerces
        // `Nat` to `Int` through `NatCast`/`Int.ofNat`; Clean's prelude has no
        // `NatCast` class (nor a `Coe Nat Int` instance) yet, so — mirroring the
        // hardcoded numeric-literal constructors elsewhere in this module — the
        // elaborator emits `Int.ofNat expr` directly, which is the SAME value
        // Lean's coercion reduces to. Ungated on the `Coe` class (like the
        // subtype step). Sound: `Int.ofNat : Nat → Int` is total and the kernel
        // re-checks the produced term.
        if let Some(coercion) = self.try_coerce_builtin_numeric(expr, &from_whnf, &to_whnf) {
            return Some(coercion);
        }

        // Step 1c: Structural coercion of a container value (e.g. a list
        // literal `[a, b]`, which the parser desugars to a `List.cons`/
        // `List.nil` chain) into the auxiliary nested-inductive type the kernel
        // synthesizes for a nested occurrence.
        //
        // For `inductive Ty | tuple : List Ty → Ty`, the kernel rewrites the
        // nested `List Ty` into an auxiliary mutual type `Ty._List` with
        // constructors `Ty._List.nil` / `Ty._List.cons` mirroring `List`. A
        // surface `Ty.tuple [Ty.int]` elaborates its argument as `List Ty`, but
        // the constructor demands `Ty._List`; the two are not defeq, so the
        // unifier (and the `Coe` lookup above) cannot bridge them. Here we
        // structurally rewrite the container value into the aux type by swapping
        // each container constructor for its aux counterpart and recursively
        // coercing the recursive (self-referential) fields. The kernel re-checks
        // the produced term, so a mismatched rewrite is rejected rather than
        // passing silently.
        if let Some(coerced) = self.try_coerce_container_to_nested_aux(expr, &from_whnf, &to_whnf) {
            return Some(coerced);
        }

        // Step 1c': Reverse direction — coerce a *value* of the auxiliary
        // nested-inductive type (`Value._List`) back into the real container
        // (`List Value`). This is the symmetric counterpart of Step 1c.
        //
        // When a constructor field has a nested-container type (`Value.vector :
        // List Value → Value`), the kernel rewrites the field type to the
        // synthesized aux mirror `Value._List`. Destructuring `.vector lanes`
        // therefore binds `lanes : Value._List`, not `List Value`. Passing
        // `lanes` to a function expecting `List Value` (e.g.
        // `executableVectorLanePayloadMatches lanes`) leaves the unifier with a
        // `Const(Value._List)` ↔ `App(List, Value)` shape mismatch the kernel
        // cannot bridge.
        //
        // The kernel already builds an axiom-free, kernel-checked conversion
        // `Value._List.toContainer : Value._List → List Value` (see
        // `inductive_to_container.rs`). Here we route the coercion through it,
        // exactly as `elab_proj.rs` does for dot-notation receivers. The kernel
        // re-checks the emitted `@<aux>.toContainer expr`, so a wrong insertion
        // fails to type-check rather than passing silently.
        if let Some(coerced) = self.try_coerce_nested_aux_to_container(expr, &from_whnf, &to_whnf) {
            return Some(coerced);
        }

        // Step 1d: Prop → Bool decision coercion (Track PP).
        //
        // When a `Bool` is expected but the value is a decidable `Prop`
        // (e.g. `a = b`, `a < b` used where a `Bool` is wanted — a match arm
        // whose branch type is `Bool`, or a `def f … : Bool := a = b`), insert
        // `@decide p inst`, mirroring Lean 4's `(p : Prop) → Bool` coercion via
        // `[Decidable p]`. We require:
        //   * `to` reduces to `Bool`,
        //   * `from` is `Prop` (`Sort 0`) — i.e. `expr` is itself the
        //     proposition being coerced, not a proof of it,
        //   * a `Decidable expr` instance resolves, and
        //   * the Bool-valued `decide` constant is present.
        // The produced term is `@decide expr inst : Bool`; the kernel re-checks
        // it, so an unsound instance simply fails to type-check.
        if matches!(to_whnf.kind(), ExprKind::Const(n, _) if n.to_string() == "Bool")
            && matches!(from_whnf.kind(), ExprKind::Sort(lvl) if lvl.is_zero())
            && self.env.get_const(&Name::from_string("decide")).is_some()
            && self.instances.is_class(&Name::from_string("Decidable"))
        {
            // The proposition to decide is the expression itself (its type is Prop).
            let prop = self.metas.instantiate(expr);
            let decidable_goal = Expr::app(
                Expr::const_(Name::from_string("Decidable"), vec![]),
                prop.clone(),
            );
            if let Some(inst_expr) = self.resolve_instance(&decidable_goal) {
                // @decide prop inst
                let coercion = Expr::app(
                    Expr::app(Expr::const_(Name::from_string("decide"), vec![]), prop),
                    inst_expr,
                );
                return Some(coercion);
            }
        }

        // Step 1e: Bool → Prop sort coercion (symmetric to Step 1d).
        //
        // When a `Prop` is expected but the value is a `Bool` (e.g. a match arm
        // `addr % size == 0` in a `Prop`-valued function, or `def p : Prop := b`),
        // insert Lean 4's `instCoeSortBoolProp`, which is `fun (b : Bool) => b = true`.
        // We build the unfolded result directly as `@Eq Bool expr Bool.true : Prop`,
        // depending only on the core `Eq`/`Bool.true` constants rather than a coercion
        // instance being registered. We require:
        //   * `to` reduces to `Prop` (`Sort 0`), and
        //   * `from` reduces to `Bool`.
        // `Bool : Type 0 = Sort 1`, so `Eq` is instantiated at level `1`. The kernel
        // re-checks the produced term, so this never weakens the kernel check.
        if matches!(to_whnf.kind(), ExprKind::Sort(lvl) if lvl.is_zero())
            && matches!(from_whnf.kind(), ExprKind::Const(n, _) if n.to_string() == "Bool")
            && self.env.get_const(&Name::from_string("Eq")).is_some()
            && self
                .env
                .get_const(&Name::from_string("Bool.true"))
                .is_some()
        {
            // @Eq.{1} Bool expr Bool.true
            let coercion = Expr::apps(
                Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
                [
                    Expr::const_str("Bool"),
                    self.metas.instantiate(expr),
                    Expr::const_str("Bool.true"),
                ],
            );
            return Some(coercion);
        }

        // Step 2: Hardcoded fallback for Nat → Real when Coe instances are
        // unavailable.
        if let (ExprKind::Const(from_name, _), ExprKind::Const(to_name, _)) =
            (from_whnf.kind(), to_whnf.kind())
        {
            if from_name.to_string() == "Nat" && to_name.to_string() == "Real" {
                // Check if Real.ofNat exists
                if self
                    .env
                    .get_const(&Name::from_string("Real.ofNat"))
                    .is_some()
                {
                    // Build: Real.ofNat expr
                    let coercion = Expr::app(
                        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
                        expr.clone(),
                    );
                    return Some(coercion);
                }
            }
        }

        None
    }

    /// Resolve a *single* `Coe <from> <to>` instance and, if found, wrap `expr`
    /// in `@Coe.coe <from> <to> <inst> <expr>`.
    ///
    /// Both `from` and `to` are expected to already be in WHNF. The caller must
    /// have verified that `Coe` is a registered class and `Coe.coe` exists.
    /// `Subtype α p → α` via `@Subtype.val.{u} α p` (Lean's `instCoeSubtype`).
    ///
    /// The receiver type `from_whnf` is matched against a saturated
    /// `@Subtype.{u} α p` application; the coercion is the first projection
    /// `Subtype.val : {α : Sort u} → {p : α → Prop} → Subtype p → α`, emitted as
    /// `@Subtype.val.{u} α p expr : α`.
    ///
    /// The universe level `u` is taken from the receiver's own `Subtype.{u}`
    /// head — NOT a fresh metavar. A fresh, unconstrained level would leave the
    /// emitted `Subtype.val.{?u}` level unsolved and the kernel would reject the
    /// term; reusing the receiver's `u` yields a level-closed coercion.
    ///
    /// Accepts only when the base `α` unifies with the expected type `to_whnf`
    /// (scoped via `push_scope`/`commit`, so a non-matching expected type leaves
    /// no partial metavar state and returns `None`).
    ///
    /// Built-in numeric widening: `Nat → Int` via `Int.ofNat`.
    ///
    /// Lean coerces `Nat` to `Int` through the `NatCast`/`CoeTail` chain
    /// (`↑n = Nat.cast n`, `NatCast Int := ⟨Int.ofNat⟩`). Clean's prelude ships
    /// neither `NatCast` nor a `Coe Nat Int` instance yet, so this hardcoded step
    /// — analogous to the built-in numeric-literal constructors in this module —
    /// emits `Int.ofNat expr` directly, the exact value Lean's coercion reduces
    /// to. It is not gated on the `Coe` class (like the subtype step), so a
    /// `def f (n : Nat) : Int := n` elaborates without a user-declared instance.
    ///
    /// Also handles `Fin n → Nat` via `@Fin.val n expr` (the structure
    /// projection, the value `i.val` Lean's `Fin`→`Nat` coercion yields), with
    /// `n` recovered from the `Fin n` source type.
    ///
    /// SOUNDNESS: `Int.ofNat : Nat → Int` and `Fin.val : Fin n → Nat` are total
    /// and the emitted term is kernel-re-checked like any other; a spurious
    /// application would be rejected rather than passing silently. No kernel/TCB
    /// code is touched.
    fn try_coerce_builtin_numeric(&self, expr: &Expr, from: &Expr, to: &Expr) -> Option<Expr> {
        let from_head = crate::coercion::head_type_name(from)?;
        let to_head = crate::coercion::head_type_name(to)?;
        if from_head == Name::from_string("Nat")
            && to_head == Name::from_string("Int")
            && self
                .env
                .get_const(&Name::from_string("Int.ofNat"))
                .is_some()
        {
            return Some(Expr::app(
                Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                expr.clone(),
            ));
        }
        // `Fin n → Nat` via `@Fin.val n expr`. `from` is `Fin n` (a single
        // application `App(Const "Fin", n)`), so recover `n` and apply the
        // projection.
        if from_head == Name::from_string("Fin")
            && to_head == Name::from_string("Nat")
            && self.env.get_const(&Name::from_string("Fin.val")).is_some()
        {
            if let ExprKind::App(fin_c, n_arg) = from.kind() {
                if matches!(fin_c.kind(), ExprKind::Const(c, _) if *c == Name::from_string("Fin")) {
                    return Some(Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Fin.val"), vec![]),
                            n_arg.as_ref().clone(),
                        ),
                        expr.clone(),
                    ));
                }
            }
        }
        None
    }

    /// SOUNDNESS: the emitted `@Subtype.val α p expr` is kernel-re-checked like
    /// any elaborated term — a wrong base or level fails to type-check rather
    /// than passing silently. No kernel/TCB code is touched.
    fn try_coerce_subtype_val(
        &mut self,
        expr: &Expr,
        from_whnf: &Expr,
        to_whnf: &Expr,
    ) -> Option<Expr> {
        // Match `@Subtype.{u} α p` (head `Const("Subtype")` applied to base +
        // predicate).
        let head = from_whnf.get_app_fn();
        let ExprKind::Const(name, levels) = head.kind() else {
            return None;
        };
        if name.to_string() != "Subtype" {
            return None;
        }
        let args = from_whnf.get_app_args();
        if args.len() != 2 {
            return None;
        }
        let alpha = args[0].clone();
        let p = args[1].clone();
        // `Subtype.val` must be available (it is, once `Subtype` is registered).
        self.env.get_const(&Name::from_string("Subtype.val"))?;
        // `@Subtype.val.{u} α p expr` — same `u` the receiver's `Subtype` carries.
        let val = Expr::const_(Name::from_string("Subtype.val"), levels.clone());
        let term = Expr::app(Expr::app(Expr::app(val, alpha.clone()), p), expr.clone());
        // Accept iff the base `α` unifies with the expected type.
        self.metas.push_scope();
        let matched = {
            let alpha_inst = self.metas.instantiate(&alpha);
            let to_inst = self.metas.instantiate(to_whnf);
            let ctx = self.build_local_ctx();
            let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
            matches!(unifier.unify(&alpha_inst, &to_inst), UnifyResult::Success)
        };
        if matched {
            self.metas.commit();
            Some(term)
        } else {
            self.metas.pop_scope();
            None
        }
    }

    fn try_coerce_coe_step(&mut self, expr: &Expr, from: &Expr, to: &Expr) -> Option<Expr> {
        let coe_goal = Expr::app(
            Expr::app(Expr::const_(Name::from_string("Coe"), vec![]), from.clone()),
            to.clone(),
        );
        let inst_expr = self.resolve_instance(&coe_goal)?;
        // Project: `@Coe.coe <from> <to> <inst> <expr>`.
        Some(Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Coe.coe"), vec![]),
                        from.clone(),
                    ),
                    to.clone(),
                ),
                inst_expr,
            ),
            expr.clone(),
        ))
    }

    /// Transitive coercion: compose imported `Coe` instances along a
    /// `from -> … -> to` path when no direct `Coe from to` instance exists.
    ///
    /// The coercion graph is built from the *registered* `Coe` instances whose
    /// source and target types both have a constant head (the imported,
    /// fully-applied shape). A BFS over those edges finds the shortest chain of
    /// intermediate types; each step is then materialized through
    /// [`Self::try_coerce_coe_step`], folding the per-step `Coe.coe` applications
    /// over `expr`.
    ///
    /// Only chains of length ≥ 2 are produced here (the direct case is handled by
    /// the single-step lookup before this is called). Parametric instances (whose
    /// source/target are not constant-headed) are excluded from the graph, so the
    /// search never speculates about types it cannot pin concretely. The kernel
    /// re-checks the resulting term, so an ill-typed composition is rejected.
    fn try_coerce_coe_chain(&mut self, expr: &Expr, from: &Expr, to: &Expr) -> Option<Expr> {
        use crate::instances::extract_class_app;

        let from_head = crate::coercion::head_type_name(from)?;
        let to_head = crate::coercion::head_type_name(to)?;
        if from_head == to_head {
            return None;
        }

        // Build the directed edge list `src_head -> (tgt_head, tgt_type)` from the
        // registered `Coe` instances with constant-headed source and target.
        let coe = Name::from_string("Coe");
        let mut edges: HashMap<Name, Vec<(Name, Expr)>> = HashMap::new();
        for inst in self.instances.get_instances(&coe) {
            let inst_ty = self.whnf(&inst.type_);
            let Some((class, args)) = extract_class_app(&inst_ty) else {
                continue;
            };
            if class != coe || args.len() != 2 {
                continue;
            }
            let src = self.whnf(&args[0]);
            let tgt = self.whnf(&args[1]);
            if let (Some(src_head), Some(tgt_head)) = (
                crate::coercion::head_type_name(&src),
                crate::coercion::head_type_name(&tgt),
            ) {
                edges.entry(src_head).or_default().push((tgt_head, tgt));
            }
        }

        // BFS for the shortest path of intermediate *types* from `from` to `to`.
        // Each queue entry carries the type sequence `[from, …, current]`.
        const MAX_COE_CHAIN_LENGTH: usize = 8;
        let mut visited: HashSet<Name> = HashSet::new();
        visited.insert(from_head.clone());
        let mut queue: VecDeque<(Name, Vec<Expr>)> = VecDeque::new();
        queue.push_back((from_head, vec![from.clone()]));

        let mut chain_types: Option<Vec<Expr>> = None;
        while let Some((current_head, types_so_far)) = queue.pop_front() {
            if types_so_far.len() > MAX_COE_CHAIN_LENGTH {
                continue;
            }
            let Some(neighbors) = edges.get(&current_head) else {
                continue;
            };
            for (next_head, next_ty) in neighbors.clone() {
                if next_head == to_head {
                    let mut full = types_so_far.clone();
                    full.push(to.clone());
                    chain_types = Some(full);
                    break;
                }
                if visited.insert(next_head.clone()) {
                    let mut extended = types_so_far.clone();
                    extended.push(next_ty);
                    queue.push_back((next_head, extended));
                }
            }
            if chain_types.is_some() {
                break;
            }
        }

        let chain_types = chain_types?;
        // A genuine chain must have at least one intermediate type (≥ 3 nodes);
        // a 2-node path is the direct case already covered by the single step.
        if chain_types.len() < 3 {
            return None;
        }

        // Fold the per-step `Coe.coe` applications over `expr`, resolving each
        // step's instance. If any step fails to resolve, abandon the chain.
        let mut acc = expr.clone();
        for window in chain_types.windows(2) {
            let step_from = self.whnf(&window[0]);
            let step_to = self.whnf(&window[1]);
            acc = self.try_coerce_coe_step(&acc, &step_from, &step_to)?;
        }
        Some(acc)
    }

    /// Coerce a value of the auxiliary nested-inductive mirror type
    /// (`<Parent>._<Container>`) back into the real container application
    /// (`<Container> args…`). This is the reverse of
    /// [`Self::try_coerce_container_to_nested_aux`].
    ///
    /// The source `from` must be (the head of) an aux type for which the kernel
    /// generated the axiom-free conversion `<aux>.toContainer : <aux> →
    /// <Container args…>` (see `inductive_to_container.rs`). The target `to` must
    /// be def-eq to that conversion's codomain — the real container application.
    /// Both are expected in WHNF.
    ///
    /// On success the emitted term is `@<aux>.toContainer.{u…} expr`, with the
    /// `toContainer` universe parameters instantiated by fresh universe metas and
    /// the result kernel re-checked against `to`. Returns `None` when no
    /// `toContainer` exists or the codomain does not match `to`, leaving the
    /// caller to report an honest mismatch. The conversion never weakens the
    /// kernel check — `toContainer` is a closed, previously kernel-checked
    /// definition and the produced application is re-checked here.
    /// If `aux` is (the head of) a nested-inductive aux mirror type
    /// (`<Parent>._<Container>`), return the *real container application* it
    /// mirrors — e.g. `Value._List` ↦ `List Value`. This reads the codomain of
    /// the kernel-generated `<aux>.toContainer : <aux> → <Container args…>`
    /// conversion, the same marker `try_coerce_nested_aux_to_container` relies
    /// on. Returns `None` when `aux` is not a bare `Const`, or has no
    /// `toContainer` conversion (i.e. it is not an aux mirror).
    ///
    /// Used to *recover the element type* an aux-mirror expected type carries so
    /// a list literal elaborated against it can pin its still-open element
    /// metavariable (`List ?α =?= Value._List` cannot pin `?α`, but `?α := Value`
    /// is exactly the container element). This is a purely informational lookup;
    /// the produced value is still kernel-re-checked downstream, so it cannot
    /// weaken soundness. The `toContainer`'s own universe params are filled with
    /// fresh universe metas so the codomain's element-universe lines up with the
    /// call site.
    pub(in crate::infer) fn aux_mirror_container_type(&mut self, aux: &Expr) -> Option<Expr> {
        let ExprKind::Const(aux_name, _) = aux.kind() else {
            return None;
        };
        let to_container_name = Name::from_string(&format!("{aux_name}.toContainer"));
        let tc_info = self.env.get_const(&to_container_name)?;
        let tc_level_params = tc_info.level_params.clone();
        let tc_type = tc_info.type_.clone();
        // `toContainer : <aux> → <Container args…>` — the codomain is the real
        // container application.
        let container_app = match tc_type.kind() {
            ExprKind::Pi(_, _, body) => (**body).clone(),
            _ => return None,
        };
        if tc_level_params.is_empty() {
            return Some(container_app);
        }
        let tc_levels: Vec<Level> = tc_level_params
            .iter()
            .map(|_| self.fresh_universe_param())
            .collect();
        Some(container_app.instantiate_level_params_direct(&tc_level_params, &tc_levels))
    }

    pub(in crate::infer) fn try_coerce_nested_aux_to_container(
        &mut self,
        expr: &Expr,
        from: &Expr,
        to: &Expr,
    ) -> Option<Expr> {
        // Source head must be a bare constant naming the aux mirror type
        // (`Value._List`). Aux types carry no value-level params/indices, so the
        // source is a bare `Const`, never an application.
        let ExprKind::Const(aux_name, _) = from.kind() else {
            return None;
        };

        // The aux type must have a generated `toContainer` conversion. Its mere
        // presence is the marker that `from` is a nested-aux mirror (the def is
        // only built for such types). Bail out otherwise.
        let to_container_name = Name::from_string(&format!("{aux_name}.toContainer"));
        let tc_info = self.env.get_const(&to_container_name)?;
        let tc_level_params = tc_info.level_params.clone();
        let tc_type = tc_info.type_.clone();

        // `toContainer : <aux> → <Container args…>`. The codomain is the real
        // container application we coerce *to*.
        let container_app = match tc_type.kind() {
            ExprKind::Pi(_, _, body) => (**body).clone(),
            _ => return None,
        };

        // Instantiate `toContainer`'s own universe params with fresh metas, so
        // the codomain's element-universe lines up with the call site.
        let tc_levels: Vec<Level> = tc_level_params
            .iter()
            .map(|_| self.fresh_universe_param())
            .collect();
        let converted = Expr::app(
            Expr::const_(to_container_name, tc_levels.clone()),
            expr.clone(),
        );
        let converted_ty = if tc_levels.is_empty() {
            container_app
        } else {
            container_app.instantiate_level_params_direct(&tc_level_params, &tc_levels)
        };

        // Re-check: the converted value's codomain must match the requested
        // target. This both confirms `to` is the matching container (not some
        // unrelated type that happens to share a head) and pins the fresh
        // universe metas.
        //
        // We use the *unifier* (not the read-only `is_def_eq`) so that a target
        // carrying an unsolved element metavar — e.g. `List ?elem`, which arises
        // when the coercion fires at a `++`/`HAppend` argument position whose
        // element type the instance has not yet pinned — gets `?elem := Value`
        // assigned from `toContainer`'s concrete codomain `List Value`. The
        // read-only `is_def_eq` cannot assign metavars and so spuriously fails
        // there, which is exactly why `xs ++ ys` over aux-typed binders leaked a
        // free variable. The assignment is made inside a scoped `push_scope` so a
        // non-matching target (`to` is not this container) leaves no partial
        // metavar state behind. SOUNDNESS is unchanged: the emitted
        // `@<aux>.toContainer expr` is the kernel-checked conversion, and the
        // unifier assignment only *resolves* the element type the kernel would
        // demand anyway — a wrong target still fails to unify and yields `None`.
        self.metas.push_scope();
        let matched = {
            let converted_ty_inst = self.metas.instantiate(&converted_ty);
            let to_inst = self.metas.instantiate(to);
            let ctx = self.build_local_ctx();
            let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
            matches!(
                unifier.unify(&converted_ty_inst, &to_inst),
                UnifyResult::Success
            )
        };
        if matched {
            self.metas.commit();
            Some(converted)
        } else {
            self.metas.pop_scope();
            None
        }
    }

    /// Structurally coerce a container value into the auxiliary nested-inductive
    /// type the kernel synthesizes for a nested occurrence.
    ///
    /// The target `to` must be (the head of) an auxiliary type named
    /// `<Parent>._<Container>` — the convention used by the nested-inductive
    /// elimination pass (`inductive_nested_elim.rs`). The source `from` must be
    /// the corresponding `<Container> ...` application. Both are expected in
    /// WHNF.
    ///
    /// The rewrite maps each `<Container>.<ctor>` constructor in `expr` to the
    /// aux constructor `<Parent>._<Container>.<ctor>`, drops the container's
    /// leading type-parameter arguments (the aux type has them substituted away),
    /// keeps non-recursive fields as-is, and recursively coerces fields whose aux
    /// type is the aux inductive itself (the `cons` tail). Returns `None` when the
    /// shapes do not line up, leaving the caller to report an honest mismatch.
    pub(in crate::infer) fn try_coerce_container_to_nested_aux(
        &mut self,
        expr: &Expr,
        from: &Expr,
        to: &Expr,
    ) -> Option<Expr> {
        // Target head must be a registered inductive whose name is `X._<Container>`.
        let ExprKind::Const(aux_name, _aux_levels) = to.get_app_fn().kind() else {
            return None;
        };
        let aux_val = self.env.get_inductive(aux_name)?.clone();

        // Source head must be a registered inductive `Container ...`.
        let ExprKind::Const(container_name, _) = from.get_app_fn().kind() else {
            return None;
        };
        let container_val = self.env.get_inductive(container_name)?.clone();

        // The aux type's last name component must be `_<Container>` — this is the
        // naming contract established by the nested-elimination pass and is what
        // ties the synthesized aux type back to its origin container.
        let aux_suffix = aux_name.last_component()?;
        let container_last = container_name.last_component()?;
        if aux_suffix != format!("_{container_last}") {
            return None;
        }

        // The aux type and the container must have matching constructor sets
        // (same suffixes, same count); otherwise this is not the mirror type and
        // we must not rewrite.
        if aux_val.constructor_names.len() != container_val.constructor_names.len() {
            return None;
        }

        // The aux constructors share the aux inductive's universe parameters;
        // reuse the levels pinned on the target type's head constant.
        let aux_levels: Vec<Level> = match to.get_app_fn().kind() {
            ExprKind::Const(_, levels) => levels.to_vec(),
            _ => Vec::new(),
        };

        // Fast path: the value is a literal container constructor chain
        // (`List.cons …`/`List.nil`). Structurally swap each ctor for its aux
        // counterpart — no recursor needed, and reductions stay transparent.
        if let Some(rewritten) =
            self.rewrite_container_value_to_aux(expr, &container_val, &aux_val, &aux_levels)
        {
            return Some(rewritten);
        }

        // General path: the value is NOT a literal chain (e.g. a free variable
        // `slots : List Value`, or `slots.set i v` / `slots.map f`). Bridge it
        // with the container's own recursor, mapping each container ctor to the
        // mirror aux ctor:
        //
        //   @<Container>.rec.{succ aux_lvl, elem_lvl} τ
        //       (fun _ => <aux>)              -- motive: const aux type
        //       <aux>.nil                      -- nil minor
        //       (fun hd _ ih => <aux>.cons hd ih)  -- cons minor
        //       expr
        //
        // This only fires for the canonical single-element `List`-shaped mirror
        // (one nullary `nil` ctor + one `cons : elem → Container → Container`).
        // The kernel re-checks the emitted closed term, so a wrong shape fails
        // to type-check rather than being silently mis-coerced.
        self.try_coerce_container_via_recursor(
            expr,
            from,
            to,
            &container_val,
            &aux_val,
            &aux_levels,
        )
    }

    /// Bridge a non-literal container value (`from = Container τ`) into its
    /// nested-aux mirror (`to = <Parent>._<Container>`) using the container's
    /// recursor. See `try_coerce_container_to_nested_aux` for the emitted shape.
    ///
    /// Returns `None` unless the container/aux pair is the canonical two-ctor
    /// `List`-style mirror (`nil`/`cons` with `cons : elem → Container → Container`).
    fn try_coerce_container_via_recursor(
        &mut self,
        expr: &Expr,
        from: &Expr,
        to: &Expr,
        container_val: &clean_kernel::inductive::InductiveVal,
        aux_val: &clean_kernel::inductive::InductiveVal,
        aux_levels: &[Level],
    ) -> Option<Expr> {
        // Element type τ: the container application's single type argument.
        let from_args = from.get_app_args();
        if from_args.len() != 1 {
            return None;
        }
        let elem_ty = from_args[0].clone();

        // Identify the container's nil/cons ctors and the matching aux ctors by
        // suffix. Require exactly the canonical two-ctor List shape.
        if container_val.constructor_names.len() != 2 || aux_val.constructor_names.len() != 2 {
            return None;
        }
        let find_by_suffix = |names: &[Name], suffix: &str| -> Option<Name> {
            names
                .iter()
                .find(|c| c.last_component().as_deref() == Some(suffix))
                .cloned()
        };
        let container_nil = find_by_suffix(&container_val.constructor_names, "nil")?;
        let container_cons = find_by_suffix(&container_val.constructor_names, "cons")?;
        let aux_nil = find_by_suffix(&aux_val.constructor_names, "nil")?;
        let aux_cons = find_by_suffix(&aux_val.constructor_names, "cons")?;

        // The cons ctor must be the standard `elem → Container → Container`
        // shape: one parameter (the element type), then two explicit fields
        // (head element, recursive tail). Anything else is not the List mirror.
        let container_cons_val = self.env.get_constructor(&container_cons)?.clone();
        if container_cons_val.num_params != 1 {
            return None;
        }

        // Universe levels. The container is universe-polymorphic in one param
        // (the element universe); its head levels pin that. The recursor's
        // motive universe is the universe the aux type *lives in*: `aux : Sort
        // motive_univ`, i.e. exactly `infer_sort(to)` (no extra `succ`).
        let container_levels: Vec<Level> = match from.get_app_fn().kind() {
            ExprKind::Const(_, levels) => levels.to_vec(),
            _ => return None,
        };
        if container_levels.len() != 1 {
            return None;
        }
        let motive_univ = self.infer_sort(to).ok()?;

        // Constants.
        let container_name = match from.get_app_fn().kind() {
            ExprKind::Const(n, _) => n.clone(),
            _ => return None,
        };
        let rec_name = Name::append(&container_name, "rec");
        self.env.get_const(&rec_name)?;
        let rec_const = Expr::const_(
            rec_name,
            vec![motive_univ.clone(), container_levels[0].clone()],
        );
        let _ = container_nil; // surfaced for clarity; the nil minor is `aux.nil`.
        let aux_ty = to.clone();
        let aux_nil_expr = Expr::const_(aux_nil, aux_levels.to_vec());
        let aux_cons_expr = Expr::const_(aux_cons, aux_levels.to_vec());

        // motive: `fun (_ : Container τ) => <aux>` (constant; aux carries no
        // params, so the motive ignores its argument).
        let container_app = from.clone();
        let motive = Expr::lam(BinderInfo::Default, container_app.clone(), aux_ty.clone());

        // cons minor: `fun (hd : τ) (_tl : Container τ) (ih : <aux>) =>
        //                <aux>.cons hd ih`.
        let cons_minor = Expr::lam(
            BinderInfo::Default,
            elem_ty.clone(),
            Expr::lam(
                BinderInfo::Default,
                container_app.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    aux_ty.clone(),
                    Expr::apps(aux_cons_expr, [Expr::bvar(2), Expr::bvar(0)]),
                ),
            ),
        );

        // @Container.rec τ motive aux.nil cons_minor expr
        let result = Expr::apps(
            rec_const,
            [elem_ty, motive, aux_nil_expr, cons_minor, expr.clone()],
        );

        // Re-check the emitted term against the target before trusting it; the
        // coercion is sugar, so an ill-typed bridge must be reported as a plain
        // mismatch rather than slipped past the kernel.
        match self.infer_type(&result) {
            Ok(ty) => {
                let ty_whnf = self.whnf(&ty);
                let to_whnf = self.whnf(to);
                if self.is_def_eq(&ty_whnf, &to_whnf) {
                    Some(result)
                } else {
                    None
                }
            }
            Err(_) => None,
        }
    }

    /// Recursively rewrite a fully-applied container constructor expression into
    /// the auxiliary type's constructors. Returns `None` if `expr` is not headed
    /// by one of the container's constructors (so a non-literal value — e.g. a
    /// free variable of type `List Ty` — is left untouched and reported as a
    /// genuine mismatch rather than silently mis-coerced).
    fn rewrite_container_value_to_aux(
        &mut self,
        expr: &Expr,
        container_val: &clean_kernel::inductive::InductiveVal,
        aux_val: &clean_kernel::inductive::InductiveVal,
        aux_levels: &[Level],
    ) -> Option<Expr> {
        let head = expr.get_app_fn();
        let ExprKind::Const(ctor_name, _) = head.kind() else {
            return None;
        };

        // Find which container constructor this is, then the matching aux ctor by
        // suffix.
        if !container_val
            .constructor_names
            .iter()
            .any(|c| c == ctor_name)
        {
            return None;
        }
        let ctor_suffix = ctor_name.last_component()?;
        let aux_ctor_name = aux_val
            .constructor_names
            .iter()
            .find(|c| c.last_component().as_deref() == Some(ctor_suffix.as_str()))?
            .clone();

        // Aux constructor field types tell us which fields are recursive
        // (self-references to the aux type) and therefore need recursion. Walk
        // the aux constructor's Pi chain, dropping its leading parameter binders.
        let aux_ctor_val = self.env.get_constructor(&aux_ctor_name)?.clone();
        let aux_field_types: Vec<Expr> = {
            let mut tys = Vec::new();
            let mut current = aux_ctor_val.type_.clone();
            let mut idx = 0u32;
            while let ExprKind::Pi(_, domain, codomain) = current.kind() {
                if idx >= aux_ctor_val.num_params {
                    tys.push(domain.as_ref().clone());
                }
                current = codomain.as_ref().clone();
                idx += 1;
            }
            tys
        };

        // Container constructor: drop its leading type-parameter arguments; the
        // remaining args correspond one-to-one with the aux constructor's fields.
        let container_ctor_val = self.env.get_constructor(ctor_name)?.clone();
        let all_args: Vec<Expr> = expr.get_app_args().into_iter().cloned().collect();
        let n_params = container_ctor_val.num_params as usize;
        if all_args.len() < n_params {
            return None;
        }
        let field_args = &all_args[n_params..];
        if field_args.len() != aux_field_types.len() {
            return None;
        }

        let mut result = Expr::const_(aux_ctor_name, aux_levels.to_vec());
        for (field_arg, aux_field_ty) in field_args.iter().zip(aux_field_types.iter()) {
            // A field whose aux type's head is the aux inductive itself is the
            // recursive (tail) field — recurse into it. All other fields (the
            // element payload) are kept verbatim.
            let aux_field_whnf = self.whnf(aux_field_ty);
            let is_recursive = matches!(
                aux_field_whnf.get_app_fn().kind(),
                ExprKind::Const(n, _) if n == &aux_val.name
            );
            let coerced_arg = if is_recursive {
                self.rewrite_container_value_to_aux(field_arg, container_val, aux_val, aux_levels)?
            } else {
                field_arg.clone()
            };
            result = Expr::app(result, coerced_arg);
        }
        Some(result)
    }

    /// Check if an expression is a Nat literal
    pub(in crate::infer) fn is_nat_literal(expr: &Expr) -> bool {
        matches!(expr.kind(), ExprKind::Lit(Literal::Nat(_)))
    }

    /// Check if a type is the Real type
    pub(in crate::infer) fn is_real_type(&self, ty: &Expr) -> bool {
        let whnf = self.whnf(ty);
        if let ExprKind::Const(name, _) = whnf.kind() {
            name.to_string() == "Real"
        } else {
            false
        }
    }

    /// Check if a type is the Nat type
    pub(in crate::infer) fn is_nat_type(&self, ty: &Expr) -> bool {
        let whnf = self.whnf(ty);
        if let ExprKind::Const(name, _) = whnf.kind() {
            name.to_string() == "Nat"
        } else {
            false
        }
    }

    /// Check if a type is the Int type
    pub(in crate::infer) fn is_int_type(&self, ty: &Expr) -> bool {
        let whnf = self.whnf(ty);
        if let ExprKind::Const(name, _) = whnf.kind() {
            name.to_string() == "Int"
        } else {
            false
        }
    }

    /// Elaborate a floating-point literal with no expected type.
    ///
    /// Defaults the target type to the prelude `Float` type, mirroring how
    /// `elab_nat_literal` defaults a bare numeral to `Nat`. The literal is
    /// lowered to `Float.ofScientific mantissa expSign decExp` (the kernel has
    /// a native reducer for this).
    pub(in crate::infer) fn elab_float_literal(&mut self, text: &str) -> Result<Expr, ElabError> {
        let float_ty = Expr::const_(Name::from_string("Float"), vec![]);
        self.elab_float_literal_with_expected(text, &float_ty)
    }

    /// Elaborate a floating-point literal against an expected type.
    ///
    /// Lean 4 elaborates float literals via the `OfScientific` typeclass:
    /// `@OfScientific.ofScientific <ty> <inst> mantissa expSign decExp`, where
    /// the triple `(mantissa, expSign, decExp)` denotes the value
    /// `mantissa * 10^(±decExp)` (with `expSign = true` meaning a negative
    /// exponent). See `parse_scientific_notation` for the decomposition.
    ///
    /// Resolution order mirrors `elab_nat_literal_with_expected`:
    /// 1. Resolve an `OfScientific <expected_ty> mantissa expSign decExp`
    ///    instance and project through `OfScientific.ofScientific` when both the
    ///    instance and the projection exist.
    /// 2. Fall back to `Float.ofScientific` directly when no instance is
    ///    available (e.g. minimal environments without the `Init` typeclasses),
    ///    matching the native kernel reducer.
    pub(in crate::infer) fn elab_float_literal_with_expected(
        &mut self,
        text: &str,
        expected_ty: &Expr,
    ) -> Result<Expr, ElabError> {
        let (mantissa, exp_sign, dec_exp) = parse_scientific_notation(text)?;
        let mantissa_lit = Expr::nat_lit(mantissa);
        let sign_lit = Expr::const_(
            Name::from_string(if exp_sign { "Bool.true" } else { "Bool.false" }),
            vec![],
        );
        let dec_exp_lit = Expr::nat_lit(dec_exp);

        let expected_whnf = self.whnf(expected_ty);

        // Step 1: Try OfScientific instance resolution against the expected type.
        // OfScientific takes (α : Type) (mantissa : Nat) (exponentSign : Bool)
        // (decimalExponent : Nat), so the goal is the full applied class type.
        if self.instances.is_class(&Name::from_string("OfScientific")) {
            let of_scientific_goal = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("OfScientific"), vec![]),
                            expected_whnf.clone(),
                        ),
                        mantissa_lit.clone(),
                    ),
                    sign_lit.clone(),
                ),
                dec_exp_lit.clone(),
            );
            if let Some(inst_expr) = self.resolve_instance(&of_scientific_goal) {
                if self
                    .env
                    .get_const(&Name::from_string("OfScientific.ofScientific"))
                    .is_some()
                {
                    // Project: `@OfScientific.ofScientific <ty> <inst> m s e`.
                    return Ok(Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::const_(
                                            Name::from_string("OfScientific.ofScientific"),
                                            vec![],
                                        ),
                                        expected_whnf,
                                    ),
                                    inst_expr,
                                ),
                                mantissa_lit,
                            ),
                            sign_lit,
                        ),
                        dec_exp_lit,
                    ));
                }
            }
        }

        // Step 2: Fall back to `Float.ofScientific` directly. This matches the
        // native kernel reducer and keeps elaboration working when the
        // environment lacks the `OfScientific` typeclass.
        Ok(Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Float.ofScientific"), vec![]),
                    mantissa_lit,
                ),
                sign_lit,
            ),
            dec_exp_lit,
        ))
    }
}

/// Decompose a lexer-produced scientific-notation float literal into the
/// `(mantissa, exponentSign, decimalExponent)` triple consumed by
/// `OfScientific.ofScientific` / `Float.ofScientific`.
///
/// The value denoted is `mantissa * 10^(±decimalExponent)`, where an
/// `exponentSign` of `true` means a negative exponent. The literal's digits are
/// preserved verbatim (Lean 4 does not normalize them): `3.14` becomes
/// `(314, true, 2)`, not `(157, true, ...)`.
///
/// Decomposition for `<int>.<frac>e<exp>`:
/// - the mantissa is the concatenation of the integer and fraction digits,
/// - the net base-10 exponent is `exp - frac.len()`,
/// - a non-negative net exponent yields `(mantissa, false, net)`,
///   a negative one yields `(mantissa, true, -net)`.
///
/// Examples: `3.14 -> (314, true, 2)`, `1e-5 -> (1, true, 5)`,
/// `2.5E10 -> (25, false, 9)`, `31.0 -> (310, true, 1)`,
/// `0.0 -> (0, true, 1)`.
///
/// The input is assumed to be a lexer-validated float token (digits, at most
/// one `.`, an optional `e`/`E` exponent with optional sign). Overflow of the
/// mantissa or the exponent magnitude is reported as a typed error rather than
/// silently wrapping or panicking.
pub(in crate::infer) fn parse_scientific_notation(
    text: &str,
) -> Result<(u64, bool, u64), ElabError> {
    let invalid = || ElabError::ParseError(format!("invalid float literal `{text}`"));

    // Split off the exponent part (after `e`/`E`), if any.
    let (significand, exp_part) = match text.find(['e', 'E']) {
        Some(idx) => (&text[..idx], Some(&text[idx + 1..])),
        None => (text, None),
    };

    let explicit_exp: i64 = match exp_part {
        Some(s) => s.parse::<i64>().map_err(|_| invalid())?,
        None => 0,
    };

    // Split the significand into integer and fractional digit runs.
    let (int_digits, frac_digits) = match significand.split_once('.') {
        Some((int, frac)) => (int, frac),
        None => (significand, ""),
    };

    if int_digits.is_empty() && frac_digits.is_empty() {
        return Err(invalid());
    }
    if !int_digits.bytes().all(|b| b.is_ascii_digit())
        || !frac_digits.bytes().all(|b| b.is_ascii_digit())
    {
        return Err(invalid());
    }

    // Mantissa is the digits with the decimal point removed.
    let mantissa_str = format!("{int_digits}{frac_digits}");
    let mantissa: u64 = mantissa_str
        .parse::<u64>()
        .map_err(|_| ElabError::Unsupported {
            feature: format!("float literal `{text}`: mantissa exceeds u64 range"),
        })?;

    // Net base-10 exponent: each fractional digit divides by ten.
    let frac_len = i64::try_from(frac_digits.len()).map_err(|_| invalid())?;
    let net_exp = explicit_exp
        .checked_sub(frac_len)
        .ok_or_else(|| ElabError::Unsupported {
            feature: format!("float literal `{text}`: exponent out of range"),
        })?;

    if net_exp >= 0 {
        let dec_exp = u64::try_from(net_exp).map_err(|_| ElabError::Unsupported {
            feature: format!("float literal `{text}`: exponent out of range"),
        })?;
        Ok((mantissa, false, dec_exp))
    } else {
        // Magnitude of a negative net exponent. Negating `i64::MIN` would
        // overflow, so route through `unsigned_abs`.
        let dec_exp = net_exp.unsigned_abs();
        Ok((mantissa, true, dec_exp))
    }
}

#[cfg(test)]
mod scientific_notation_tests {
    use super::parse_scientific_notation;
    use crate::error::ElabError;

    #[test]
    fn test_parse_scientific_notation_decimal_negates_fraction_exponent() {
        // `3.14` = 314 * 10^-2.
        assert_eq!(
            parse_scientific_notation("3.14").expect("valid float"),
            (314, true, 2)
        );
    }

    #[test]
    fn test_parse_scientific_notation_pure_negative_exponent() {
        // `1e-5` = 1 * 10^-5.
        assert_eq!(
            parse_scientific_notation("1e-5").expect("valid float"),
            (1, true, 5)
        );
    }

    #[test]
    fn test_parse_scientific_notation_positive_exponent_with_fraction() {
        // `2.5E10` = 25 * 10^9 (net exponent 10 - 1 = 9, non-negative).
        assert_eq!(
            parse_scientific_notation("2.5E10").expect("valid float"),
            (25, false, 9)
        );
    }

    #[test]
    fn test_parse_scientific_notation_trailing_zero_preserves_digits() {
        // `31.0` keeps the literal digits: 310 * 10^-1, not 31 * 10^0.
        assert_eq!(
            parse_scientific_notation("31.0").expect("valid float"),
            (310, true, 1)
        );
    }

    #[test]
    fn test_parse_scientific_notation_zero_decimal() {
        // `0.0` = 0 * 10^-1.
        assert_eq!(
            parse_scientific_notation("0.0").expect("valid float"),
            (0, true, 1)
        );
    }

    #[test]
    fn test_parse_scientific_notation_positive_signed_exponent() {
        // `1.5e+3` = 15 * 10^2 (net 3 - 1 = 2).
        assert_eq!(
            parse_scientific_notation("1.5e+3").expect("valid float"),
            (15, false, 2)
        );
    }

    #[test]
    fn test_parse_scientific_notation_integer_with_exponent_only() {
        // `2e3` = 2 * 10^3, no fractional part.
        assert_eq!(
            parse_scientific_notation("2e3").expect("valid float"),
            (2, false, 3)
        );
    }

    #[test]
    fn test_parse_scientific_notation_mantissa_overflow_is_unsupported() {
        // A mantissa beyond u64 range is reported as a typed error, not a panic.
        let huge = "9".repeat(40);
        match parse_scientific_notation(&huge) {
            Err(ElabError::Unsupported { feature }) => {
                assert!(
                    feature.contains("mantissa"),
                    "unexpected feature: {feature}"
                );
            }
            other => panic!("expected Unsupported for mantissa overflow, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_scientific_notation_bad_exponent_is_parse_error() {
        // A non-numeric exponent (should not reach here from the lexer, but the
        // function must fail closed rather than panic).
        match parse_scientific_notation("1eZ") {
            Err(ElabError::ParseError(msg)) => {
                assert!(msg.contains("invalid float literal"), "unexpected: {msg}");
            }
            other => panic!("expected ParseError for bad exponent, got {other:?}"),
        }
    }
}

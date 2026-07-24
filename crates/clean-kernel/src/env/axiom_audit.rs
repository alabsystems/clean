// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof soundness metrics: axiom dependency analysis and proof quality classification.
//!
//! Prevents fake proofs where theorems wrap unproved axioms. Agents "proved"
//! 15 conjectures by registering axioms and wrapping them in `Declaration::Theorem`.
//! The kernel type-checks the wrapper, but the mathematical content is in the
//! axioms. This module makes that measurable.
//!
//! # Key APIs
//!
//! - [`Environment::axiom_deps`] — transitive domain-axiom dependencies for any declaration
//! - [`Environment::proof_quality`] — classification: Constructive / AxiomDependent / NotATheorem / Unchecked
//! - [`Environment::soundness_report`] — whole-environment proof quality summary

use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use hashbrown::HashSet;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::types::{ConstantInfo, ConstantKind, Declaration};
use super::{DeclarationVerification, Environment};

/// Lean 4 foundational axioms that are NOT counted as domain-specific trust gaps.
///
/// These are part of the Lean 4 logical foundation and are always accepted.
/// Any axiom not in this list is considered a domain-specific axiom that represents
/// an unproved assumption.
pub(crate) const FOUNDATIONAL_AXIOMS: &[&str] = &[
    // Propositional extensionality
    "propext",
    // Quotient type axiom
    "Quot.sound",
    // Classical choice
    "Classical.choice",
    // Equality. `Eq.refl` is the canonical constructor of the `Eq` inductive
    // type (`core_eq/recursors.rs` registers it via `Constructor`), so its
    // `ConstantKind` is `Constructor`, not `Axiom` — whitelisting it here is
    // harmless but matches historical convention.
    //
    // NOTE (#3559): `Eq.symm`, `Eq.trans`, and `Eq.subst` were previously
    // listed here under the same "Equality axioms" block, but are registered
    // as `Declaration::Theorem` with genuine kernel-checked proof terms in
    // `core_eq/basic.rs` (`register_symm`, `register_trans`, `register_subst`
    // via `decl_emit::theorem`). The BFS in `axiom_deps` short-circuits on
    // `kind == Axiom`, so the whitelist entries for these names were dead
    // code that could silently mask a future demotion regression. Removed by
    // #3559. The disjointness invariant is pinned by
    // `test_foundational_axioms_disjoint_from_theorems` in
    // `tests_axiom_audit.rs`.
    "Eq.refl",
    // Proof irrelevance
    "proofIrrel",
    // NOTE: `funext` was previously listed here as a foundational axiom, but is
    // now a kernel-checked `Declaration::Theorem` derived from `Quot.sound`
    // exactly as Lean 4 core derives it (see `Environment::init_funext` /
    // `funext_proof_value`). Per the #3559 precedent (Eq.symm/Eq.trans/Eq.subst),
    // a whitelist entry for a `Declaration::Theorem` is dead code — the
    // `axiom_deps` BFS short-circuits on `kind == Axiom` — and could silently
    // mask a future demotion regression, so the entry was removed. funext's
    // transitive axiom closure now reaches `Quot.sound` (still foundational).
    // The disjointness invariant is pinned by
    // `test_foundational_axioms_disjoint_from_theorems` and the positive half by
    // `test_promoted_theorems_are_not_foundational_and_are_theorems`.
    // Quotient primitives
    "Quot",
    "Quot.mk",
    "Quot.ind",
    "Quot.lift",
    // Well-founded recursion
    "WellFounded.fix",
    // String/char representation axioms.
    //
    // `Char.decEq` is NO LONGER an axiom: `Char` is the genuine v4.30 2-field
    // structure `Char.mk (val : UInt32) (valid : val.isValidChar)` (carrier-
    // parity P2), so `register_char_dec_eq_proof` (`algebra_uint_dec_eq_proof.rs`)
    // builds it as an axiom-free, kernel-checked `Definition` — `Char.rec`
    // destructure both operands, dispatch on `UInt32.decEq` of the `val`s, lift
    // `isTrue` via `Eq.rec` + proof irrelevance of the `valid` field and discharge
    // `isFalse` via `congrArg Char.val`. It is absent from the live
    // `soundness_tcb.json` census. The name is retained in this whitelist only as
    // a no-op (a constant that is not an axiom is trivially within the
    // foundational-axiom allowance).
    "Char.decEq",
    // `String.decEq` is NO LONGER an axiom: `String.mk : List Char → String` is a
    // single-field structure wrapping a `List Char`, so the recursive
    // `(List Char).decEq` decision procedure (`ListChar.decEq`,
    // `algebra_list_char_dec_eq_proof.rs`: nil/nil → isTrue, nil/cons & cons/nil →
    // isFalse via `List.noConfusion`, cons/cons → conjoin `Char.decEq` on heads
    // with the recursive tail decision, lifting through `List.cons` injectivity)
    // now backs a constructive, kernel-checked `String.decEq` Definition over the
    // faithful carrier (`algebra_string_dec_eq_proof.rs`): destructure `a`/`b` via
    // `String.rec`, dispatch on `ListChar.decEq (String.data a)(String.data b)`,
    // `isTrue` lifts via `congrArg String.mk`, `isFalse` refutes via
    // `congrArg String.data`. It is absent from the live `soundness_tcb.json`
    // census. The name is retained in this whitelist only as a no-op (a constant
    // that is not an axiom is trivially within the foundational-axiom allowance).
    "String.decEq",
    // (TCB-shrink: `instDecidableEqFin` ELIMINATED — now a computable, axiom-free
    // `Declaration::Definition` (`algebra_fin_dec_eq_proof.rs`) deciding
    // `Eq (Fin n) a b` via `Nat.decEq (Fin.val a)(Fin.val b)` over the faithful
    // `Fin` carrier: `isTrue` lifts through `Fin.eq_of_val_eq` (struct-eta +
    // proof-irrelevance of the `isLt` field), `isFalse` refutes via
    // `congrArg Fin.val`. No longer an axiom, removed from this whitelist.)
    // Decidable classical.
    //
    // DIACONESCU (foundational census −2): `Classical.em` and
    // `Classical.byContradiction` are NO LONGER axioms. They are now
    // kernel-CHECKED `Declaration::Theorem`s built in
    // `classical_em_proof.rs` (Diaconescu's theorem): `em` is proved from
    // `Classical.choice` + `propext` + `funext`, and `byContradiction` from
    // `em`. Their transitive axiom closures are `⊆ FOUNDATIONAL_AXIOMS`
    // (`{propext, funext, Classical.choice}` plus the `Eq`/`Quot`/`Subtype`
    // recursor primitives), so theorems reaching them stay `Constructive`.
    // Per the #3559 disjointness rule (whitelist entries for Theorems are
    // dead code that could silently mask a demotion regression), both names
    // are removed from this list; `init_classical` registers them via a
    // guarded swap (theorem-first, axiom-fallback). The
    // `test_foundational_axioms_disjoint_from_theorems` invariant pins this.
    // NOTE: `sorry` / `sorryAx` / `trustedArith` / `trustedAy` are NOT
    // foundational — they live in `TRUST_MARKERS` (see below). A theorem
    // whose transitive closure reaches a trust marker is NOT
    // `ProofQuality::Constructive`. Prior to #3554 `sorryAx` was
    // mis-listed here, which caused the classifier to drop `sorryAx` from
    // the returned deps set and report sorry-reaching proofs as
    // constructive. See #3554 + `TRUST_MARKERS` for the fix.
    // Rat ordering axioms — standard properties of ordered fields.
    // Lean 4 Mathlib proves these constructively from the field axioms.
    // Listed as foundational because they are mathematical tautologies
    // about rational number ordering, not domain-specific assumptions.
    //
    // NOTE (#3470 Lane #2/#3): `Rat.le_refl`, `Rat.le_total`,
    // `Rat.zero_lt_one`, and `Rat.lt_iff_le_not_le` have been GENUINELY
    // ELIMINATED — they are now kernel-checked `Declaration::Theorem`s
    // (`algebra_rat_order_proofs.rs::register_rat_order_proofs`) over the
    // reducible `Rat.le`/`Rat.lt` Int-comparison Definitions:
    //   - `Rat.le_refl`  := `λ a => @Int.le_refl (cross a a)`  (Constructive)
    //   - `Rat.le_total` := `λ a b => @Int.le_total (cross a b) (cross b a)`
    //                       (Constructive)
    //   - `Rat.zero_lt_one` := `@Int.NonNeg.mk Nat.zero` (Constructive)
    //   - `Rat.lt_iff_le_not_le` := `λ a b => @Int.lt_iff_le_not_le
    //       (cross a b) (cross b a)` (AxiomDependent on the still-admitted
    //       `Int.lt_iff_le_not_le`; no fresh Rat axiom).
    // Per the #3559 disjointness rule (whitelist entries for Theorems are dead
    // code that could silently mask a demotion regression), all four entries
    // have been removed from this whitelist and from `ADMITTED_DOMAIN_AXIOMS`.
    // The `test_foundational_axioms_disjoint_from_theorems` test in
    // `tests_axiom_audit.rs` pins this. `Rat.mul_pos` is ALSO genuinely
    // eliminated (a kernel-checked Theorem reducing to the constructive
    // `Int.mul_pos` — the denominators drop out because
    // `Rat.num Rat.zero ≡ Int.zero`), so it is removed too.
    //
    // SOUNDNESS FIX: `Rat.le_trans` was previously listed here as an admitted
    // `Declaration::Axiom`, but it was PROVABLY FALSE under the free-inductive
    // `Rat.mk : Int -> Nat` carrier (no `denom > 0` invariant — e.g.
    // `mk 5 1 ≤ mk 0 0 ≤ mk (-5) 1` both hold under naive cross-multiplication
    // yet `mk 5 1 ≤ mk (-5) 1` is false). `Rat.le` / `Rat.lt` are now defined
    // over the EFFECTIVE denominator (`Rat.effDenom`, never 0; definitionally
    // `denom` for well-formed Rats) and `Rat.le_trans` is a GENUINE
    // kernel-checked `Declaration::Theorem` (see `algebra_rat_le_trans_proof.rs`,
    // reducing to the constructive `Int.le_cross_trans`). Per the #3559
    // disjointness rule the entry is removed here AND from
    // `ADMITTED_DOMAIN_AXIOMS`; `test_foundational_axioms_disjoint_from_theorems`
    // pins this.
    //
    // SOUNDNESS / honesty (Rat.mul_nonneg ELIMINATED): `Rat.mul_nonneg` was
    // previously admitted here, but it is now a GENUINE kernel-checked
    // `Declaration::Theorem` (see `algebra_rat_order_proofs.rs::
    // register_rat_mul_nonneg`) — the exact `Rat.le` analog of the proven
    // `Rat.mul_pos`. Provable WITHOUT denominator cancellation (and without the
    // unsound `Rat.mk_eq_mk_of_cross_eq` bridge) because `Rat.num Rat.zero ≡
    // Int.zero` collapses every `Rat.le Rat.zero _` to an `Int.le Int.zero _`,
    // which the constructive `Int.mul_nonneg` discharges (with `Int.zero_mul` /
    // `Int.mul_one` transports). Per the #3559 disjointness rule the entry is
    // removed here AND from `ADMITTED_DOMAIN_AXIOMS`;
    // `test_foundational_axioms_disjoint_from_theorems` pins this.
    //
    // The remaining three are all PROVABLY FALSE on the zero-denominator free
    // `Rat.mk : Int → Nat` carrier — they are admitted (unconditional) axioms
    // that are NOT theorems and CANNOT be proven as stated; they require a
    // normalized/quotient Rat (denom>0) carrier. OUT OF SCOPE here. Kernel-
    // confirmed counterexamples are pinned by the regression tests in
    // `tests_rat_false_add_axioms.rs`:
    //   - `Rat.le_antisymm`: `le a b ∧ le b a` does not imply syntactic
    //     `a = b` (e.g. `mk 1 2` vs `mk 2 4` cross-equal but distinct ctors).
    //   - `Rat.add_le_add_left`: `a=mk 0 2, b=mk 0 1, c=mk 1 0` — `le a b`
    //     reduces to `Int.le 0 0` (TRUE) but `le (c+a) (c+b)` reduces to
    //     `Int.le 2 1` (FALSE). `Rat.add`'s denominator `Nat.mul (denom a)
    //     (denom b)` collapses to 0 for the denom-0 `c`, then `effDenom`
    //     rescues it to 1 and the bare numerators are compared.
    //   - `Rat.le_add_of_nonneg_right`: `a=mk 1 1, b=mk 0 0` — `le 0 b`
    //     reduces to `Int.le 0 0` (TRUE) but `le a (a+b)` reduces to
    //     `Int.le 1 0` (FALSE), same `Rat.add` denom-collapse mechanism.
    // Unlike `Rat.le_trans` (false via `Rat.le`, repaired by the effDenom
    // redefinition of `Rat.le`), these are false via `Rat.add`, and the
    // analogous effDenom redefinition of `Rat.add` is NOT viable: it would turn
    // the currently-TRUE theorems `Rat.zero_add` / `Rat.add_zero` FALSE (for a
    // denom-0 `a`, `0 + a` would become `mk (num a) 1 ≠ mk (num a) 0 = a`).
    // They stay admitted with this honest FALSE-on-free-carrier classification
    // until a normalized Rat carrier lands.
    //
    // WS-A ATOMIC LIVE SWITCH: `Rat.le_antisymm`, `Rat.add_le_add_left`,
    // `Rat.le_add_of_nonneg_right` are ELIMINATED — the live `Rat` is now the
    // quotient carrier `Rat := Quot Rat.Raw.Equiv`, over which they are genuine
    // kernel-checked `Declaration::Theorem`s (`Constructive`, closure ⊆
    // FOUNDATIONAL via `Quot.sound`/`propext`). Removed from this list per the
    // #3559 disjointness rule; theorem-kind is pinned by the payoff tests in
    // `algebra_rat_quotient.rs` and the flipped `tests_rat_false_add_axioms.rs`.
    // WS-B: the Rat min/max axioms (`Rat.max` / `Rat.min` / `Rat.max_def` /
    // `Rat.max_def'` / `Rat.min_def` / `Rat.min_def'`) and the six lattice
    // characterization lemmas (`Rat.le_max_left` / `Rat.le_max_right` /
    // `Rat.min_le_left` / `Rat.min_le_right` / `Rat.max_le` / `Rat.le_min`)
    // were ELIMINATED to kernel-checked constructive Definitions/Theorems over
    // the quotient carrier (`algebra_rat_minmax_proof.rs`): `Rat.min`/`Rat.max`
    // are reducible `Declaration::Definition`s (`@Bool.rec _ _ _ (Rat.ble a b)`)
    // and the ten equations/inequalities are `Constructive`
    // `Declaration::Theorem`s. Per the #3559 disjointness rule a Theorem name
    // must NOT appear in this whitelist (pinned by
    // `test_foundational_axioms_disjoint_from_theorems`), so all 12 have been
    // removed.
    // (#3470: `Fin.castSucc` and `Fin.last` were ELIMINATED — they are now
    // computable `Declaration::Definition`s over `Fin.mk`/`Fin.val`/`Fin.rec`,
    // not axioms, so they no longer appear in any axiom closure. Removed from
    // this whitelist. See `nn_verify_fin_sum.rs`.)
    // Rat commutative-ring axioms (additive monoid). These are the standard
    // Mathlib abelian-group axioms over `Rat`, structurally identical to the
    // already-whitelisted `Rat.le_refl` etc.: each is registered with its
    // canonical Mathlib type signature (e.g. `∀ a b : Rat, a + b = b + a`)
    // in `crates/clean-kernel/src/env/algebra_field_inst.rs` with no trust
    // envelope, no `sorry`, and no domain content. Mathlib proves them
    // constructively from the field axioms; the opaque-axiom form is
    // exported for ergonomic kernel use. Promoting them unblocks
    // `Rat.sub_nonneg_of_le`, `Rat.le_of_sub_nonneg`, `Rat.sub_self`,
    // `NNVerify.add_le_add`, `NNVerify.mul_nonneg_le_left`, and
    // `NNVerify.mul_nonpos_le_left` (Tier D axiom-reject triage — #3551).
    // NOTE (#3572 Phase 2): `Rat.add_comm` was previously listed here when
    // it was a `Declaration::Axiom`. It is now a `Declaration::Theorem`
    // (see `algebra_rat_add_comm_proof.rs`), with a constructive proof over
    // `Int.add_comm` + `Nat.mul_comm`. Per the #3559 disjointness rule
    // (whitelist entries for Theorems are dead code that could silently
    // mask a demotion regression), the entry has been removed. The
    // `test_foundational_axioms_disjoint_from_theorems` test in
    // `tests_axiom_audit.rs` pins this; the theorem-kind is pinned by
    // `test_rat_add_comm_is_theorem_not_axiom` in the companion test
    // module `tests_algebra_rat_add_comm.rs`.
    //
    // NOTE (#3572 Phase 3): `Rat.add_assoc` was previously listed here when
    // it was a `Declaration::Axiom`. It is now a `Declaration::Theorem`
    // (see `algebra_rat_add_assoc_proof.rs`), with a constructive proof
    // over Int ring-normalization (`Int.right_distrib`, `Int.mul_assoc`,
    // `Int.mul_comm`, `Int.add_assoc`, `Int.ofNat_mul`) + `Nat.mul_assoc`.
    // Per the #3559 disjointness rule the whitelist entry has been removed.
    // The `test_foundational_axioms_disjoint_from_theorems` test in
    // `tests_axiom_audit.rs` pins this; the theorem-kind is pinned by
    // `test_rat_add_assoc_is_theorem_not_axiom` in the companion test
    // module `tests_algebra_rat_add_assoc.rs`.
    // NOTE (#3581 Phase 2): `Rat.zero_add` and `Rat.add_zero` were previously
    // listed here as `Declaration::Axiom`. They are now `Declaration::Theorem`
    // entries (see `algebra_rat_tranche_b_proofs.rs`), with constructive
    // proofs built from `Int.zero_mul` / `Int.zero_add` / `Int.mul_one` /
    // `Int.mul_zero` / `Int.add_zero` / `Nat.one_mul` / `Nat.mul_one` +
    // `congrArg` + `Eq.trans` chains into `Rat.mk`. Per the #3559
    // disjointness rule, they have been removed from this whitelist. The
    // `test_foundational_axioms_disjoint_from_theorems` test in
    // `tests_axiom_audit.rs` pins this.
    //
    // WS-A ATOMIC LIVE SWITCH: `Rat.add_left_neg`, `Rat.add_neg_self`,
    // `Rat.add_right_cancel` are ELIMINATED to genuine quotient
    // `Declaration::Theorem`s and removed from this list (see the payoff
    // registration in `algebra_rat_quotient.rs`).
    // NOTE (#3656 / #3657): `Rat.left_distrib` briefly became a
    // bridge-backed `Declaration::Theorem`, but #3654 established that the
    // `Rat.mk_eq_mk_of_cross_eq` bridge is unsound under the current
    // free-inductive `Rat` carrier. The live initializer now leaves the
    // bridge unregistered, and `Rat.left_distrib` remains a plain
    // `Declaration::Axiom` outside `FOUNDATIONAL_AXIOMS` so downstream
    // theorem closures continue to expose the trust gap directly
    // (`Rat.mul_sub` should classify as `AxiomDependent` on
    // `Rat.left_distrib`, not `Constructive`).
    // NOTE (#3572 Phase 1): `Rat.mul_comm` was previously listed here when
    // it was a `Declaration::Axiom`. It is now a `Declaration::Theorem`
    // (see `algebra_rat_mul_comm_proof.rs`), with a constructive proof over
    // `Int.mul_comm` + `Nat.mul_comm`. Per the #3559 disjointness rule
    // (whitelist entries for Theorems are dead code that could silently
    // mask a demotion regression), the entry has been removed. The
    // `test_foundational_axioms_disjoint_from_theorems` test in
    // `tests_axiom_audit.rs` pins this.
    //
    // NOTE (#3470 Lane #2/#3): `Rat.mul_neg` was previously listed here as a
    // `Declaration::Axiom`. It is now a `Declaration::Theorem` with a
    // constructive proof (`congrArg (fun x => Rat.mk x D)` over the symm of
    // `Int.neg_mul_right`); see
    // `nn_verify_rat_ordering.rs::register_rat_mul_neg`. Per the #3559
    // disjointness rule, the entry has been removed.
    // Rat multiplicative commutative-ring / field axioms. These are the
    // remaining Rat field axioms registered in
    // `crates/clean-kernel/src/env/algebra_field_inst.rs` (sites 200-544)
    // that were NOT already whitelisted under the additive-monoid and
    // additive-inverse batches above. Each is a standard Mathlib field
    // axiom (`Rat.one_mul`,
    // `Rat.mul_one`: multiplicative identity; `Rat.zero_mul`,
    // `Rat.mul_zero`: zero annihilation; `Rat.right_distrib`:
    // `(a+b)*c = a*c + b*c`; `Rat.mul_inv_cancel`:
    // `a ≠ 0 → a * a⁻¹ = 1`; `Rat.inv_zero`: `0⁻¹ = 0` by Mathlib
    // convention). Registered as plain `Declaration::Axiom` with
    // canonical type signatures — no trust envelope, no `sorry`, no
    // domain content. Mathlib proves them constructively from the
    // Rat quotient carrier `Rat := Int × Nat* / ≈`; the opaque-axiom
    // form is exported for ergonomic kernel use until the constructive
    // carrier proofs land (tracker: epic #3470). Promoting them
    // completes the Rat field axiom tranche (#3555) and unblocks
    // downstream Tier A Rat algebra lemmas that compose through
    // multiplication, distributivity, or inversion.
    // NOTE (Part of #3582, Tranche C Phase 3): `Rat.mul_assoc` was previously
    // listed here when it was a `Declaration::Axiom`. It is now a
    // `Declaration::Theorem` (see `algebra_rat_mul_assoc_proof.rs`), with a
    // constructive proof over `Int.mul_assoc` + `Nat.mul_assoc`. Per the
    // #3559 disjointness rule, the entry has been removed. The
    // `test_foundational_axioms_disjoint_from_theorems` test in
    // `tests_axiom_audit.rs` pins this; the theorem-kind is pinned by
    // `test_rat_mul_assoc_is_theorem_not_axiom` in the companion test
    // module `tests_algebra_rat_mul_assoc.rs`.
    // NOTE (#3581 Phase 2): `Rat.one_mul` and `Rat.mul_one` were previously
    // listed here as `Declaration::Axiom`. They are now `Declaration::Theorem`
    // entries (see `algebra_rat_tranche_b_proofs.rs`), with constructive
    // proofs built from `Int.one_mul` / `Int.mul_one` + `Nat.one_mul` /
    // `Nat.mul_one` chained via `congrArg` + `Eq.trans` into `Rat.mk`.
    // Per the #3559 disjointness rule, they have been removed from this
    // whitelist. #3656 rolls `Rat.zero_mul` and `Rat.mul_zero` back from the
    // unsound bridge-backed theorem experiment to their prior
    // `Declaration::Axiom` status, so both names re-enter this whitelist.
    //
    // WS-A ATOMIC LIVE SWITCH: `Rat.zero_mul`, `Rat.mul_zero`,
    // `Rat.right_distrib`, `Rat.mul_inv_cancel` (and `Rat.left_distrib`) are
    // ELIMINATED to genuine quotient `Declaration::Theorem`s (`Constructive`),
    // so they are removed from this list. The quotient identifies equivalent
    // representatives, making the structural-equality claims TRUE.
    // NOTE (#3581 Phase 1): `Rat.inv_zero` was previously listed here as a
    // `Declaration::Axiom`. It is now a `Declaration::Theorem` with a
    // genuine `Eq.refl`-based proof (see `algebra_rat_tranche_b_proofs.rs`).
    // Per the #3559 disjointness rule, the whitelist entry has been
    // removed. The `test_foundational_axioms_disjoint_from_theorems` test
    // in `tests_axiom_audit.rs` pins this.
    // NOTE (#3559): `Rat.add_le_add` and `Rat.neg_le_neg` were previously
    // listed here under the same batch, but have since been promoted to
    // `Declaration::Theorem` with genuine kernel-checked proof terms in
    // `nn_verify_interval_arith_proofs.rs::register_rat_add_le_add`
    // (#3537) and `::register_rat_neg_le_neg` (#3538). The BFS in
    // `axiom_deps` short-circuits on `kind == Axiom`, so the whitelist
    // entries for these names were dead code that could silently mask a
    // future demotion regression. Removed by #3559. The disjointness
    // invariant between FOUNDATIONAL_AXIOMS and registered Theorems is
    // pinned by `test_foundational_axioms_disjoint_from_theorems` in
    // `tests_axiom_audit.rs`.
    //
    // NOTE (#3599): `Nat.le_refl` was previously listed here as a
    // `Declaration::Axiom`. It is now registered as a
    // `Declaration::Theorem` with a constructive proof term
    // `fun n => @Nat.le.refl n` in
    // `nat_top_level_ordering_proof.rs::register_nat_le_refl_theorem`.
    // Per the #3559 disjointness rule, the whitelist entry has been
    // removed; the disjointness invariant is pinned by
    // `test_foundational_axioms_disjoint_from_theorems`.
    // Nat bitwise primitives (Tier D, #3548). Lean 4 itself axiomatizes
    // these as kernel-level bitwise operations; they cannot be defined
    // via `Nat.rec` alone because arbitrary-precision bitwise operations
    // require access to the underlying big-integer representation. Lean 4
    // / Mathlib compile them to native `UInt`/`BigInt` ops at runtime and
    // treat them as opaque primitives for kernel reasoning. Registered as
    // plain `Declaration::Axiom` in
    // `crates/clean-kernel/src/env/data_types_nat.rs:556-584` with the
    // canonical Lean 4 signatures:
    //   `Nat.{land,lor,xor,shiftLeft,shiftRight} : Nat → Nat → Nat`
    //   `Nat.testBit : Nat → Nat → Bool`
    // Computation is handled by `init_arith_native_reducers` (see #3396).
    // No trust envelope, no `sorry`, no mathematical content beyond the
    // Lean 4 primitive — requiring a kernel proof is a category error.
    // Per the 2026-04-19 Tier D triage design
    // (`designs/2026-04-19-foundational-axiom-whitelist-expansion.md` §2,
    // Category 2), these axioms were foundational-by-definition.
    // (Track II: `Nat.land`/`Nat.lor`/`Nat.xor` ELIMINATED — discharged to real
    // reducible Definitions `Nat.bitwise and/or/xor` (a total fuel fold over
    // `Nat.div2`/`Nat.testBit`), with the bit-extension theorem
    // `Nat.testBit_bitwise`. See `algebra_nat_bitwise_def.rs`. Removed.)
    // (#3470: `Nat.shiftLeft` ELIMINATED — now a computable Definition via
    // `Nat.rec` + `Nat.mul` (= multiply by 2^n), not an axiom. Removed.)
    // (TCB-shrink Tier-0: `Nat.shiftRight` ELIMINATED — now a computable
    // Definition `fun m n => Nat.iterDiv2 n m` (= m / 2^n) via
    // `algebra_nat_bitwise_def.rs::register_nat_shiftright_def`, not an axiom.
    // Removed.)
    // (Track FF step 1: `Nat.testBit` ELIMINATED — now a computable Definition
    // (parity of the i-fold `Nat.div2` of n) via `algebra_nat_testbit_def.rs`,
    // not an axiom. Removed.)
];

/// Admitted DOMAIN axioms — mathematically true (provable in Lean 4 Mathlib)
/// but registered here as bare `Declaration::Axiom` with NO Clean-kernel proof
/// term. They were historically listed in `FOUNDATIONAL_AXIOMS` for ergonomic
/// "ergonomic kernel use" (epics #3470/#3490/#3543), which caused the
/// integrity defect that theorems resting on them were reported as
/// `ProofQuality::Constructive` ("genuinely proved, no domain-specific axiom
/// dependencies") — an overstatement, since the dependency is real and unproved
/// in THIS kernel. They are now EXCLUDED from `is_foundational_axiom`, so a
/// theorem whose transitive closure reaches one of them honestly classifies as
/// `AxiomDependent` (listing the admitted axiom) rather than `Constructive`.
/// They remain in `FOUNDATIONAL_AXIOMS` purely so the existing disjointness /
/// documentation invariants keep tracking them; the exclusion below is the
/// single source of truth for the Constructive gate.
pub(crate) const ADMITTED_DOMAIN_AXIOMS: &[&str] = &[
    // Rat ordered-field ordering.
    // (#3470 Lane #2/#3: `Rat.le_refl`, `Rat.le_total`, `Rat.zero_lt_one`,
    // `Rat.lt_iff_le_not_le`, `Rat.mul_pos` ELIMINATED to kernel-checked
    // `Declaration::Theorem`s in `algebra_rat_order_proofs.rs`; removed from this
    // list. `le_refl`/`le_total`/`zero_lt_one`/`mul_pos` are `Constructive`;
    // `lt_iff_le_not_le` is honestly `AxiomDependent` on the still-admitted
    // `Int.lt_iff_le_not_le`.)
    //
    // SOUNDNESS FIX: `Rat.le_trans` ELIMINATED — it was a FALSE axiom under the
    // free-inductive `Rat` carrier and is now a genuine kernel-checked
    // `Declaration::Theorem` over the effective-denominator `Rat.le`
    // (`algebra_rat_le_trans_proof.rs`, `Constructive`). Removed from this list.
    //
    // `Rat.mul_nonneg` ELIMINATED — now a genuine kernel-checked
    // `Declaration::Theorem` (`algebra_rat_order_proofs.rs::
    // register_rat_mul_nonneg`, `Constructive`), the `Rat.le` analog of the
    // proven `Rat.mul_pos`: `Rat.num Rat.zero ≡ Int.zero` collapses every
    // `Rat.le Rat.zero _` to `Int.le Int.zero _`, discharged by the constructive
    // `Int.mul_nonneg`. Removed from this list (and from `FOUNDATIONAL_AXIOMS`).
    //
    // WS-A ATOMIC LIVE SWITCH: `Rat.le_antisymm`, `Rat.add_le_add_left`,
    // `Rat.le_add_of_nonneg_right` (all FALSE over the free carrier) ELIMINATED
    // to genuine quotient `Declaration::Theorem`s; removed from this list.
    //
    // WS-B: the Rat min/max + lattice axioms ELIMINATED to kernel-checked
    // constructive Definitions/Theorems over the quotient carrier
    // (`algebra_rat_minmax_proof.rs`). `Rat.min` / `Rat.max` are reducible
    // `Declaration::Definition`s (`@Bool.rec _ _ _ (Rat.ble a b)`); the four
    // characterizing equations `Rat.{min,max}_def{,'}` and the six lattice
    // lemmas `Rat.le_max_left` / `Rat.le_max_right` / `Rat.min_le_left` /
    // `Rat.min_le_right` / `Rat.max_le` / `Rat.le_min` are `Constructive`
    // `Declaration::Theorem`s (case-split on the decidable `Rat.ble` order,
    // discharged by the landed quotient `Rat.le_refl`/`le_total`/`le_antisymm`).
    // All 12 removed from this list.
    // Rat ring/field
    // (#3470 Lane #2/#3: `Rat.mul_neg` ELIMINATED to a kernel-checked
    // `Declaration::Theorem` via `congrArg` over `Int.neg_mul_right`; removed.)
    //
    // WS-A ATOMIC LIVE SWITCH: the additive-inverse, cancellation, zero-mul,
    // distributivity and inverse-cancel `Rat.*` axioms (`Rat.add_left_neg`,
    // `Rat.add_neg_self`, `Rat.add_right_cancel`, `Rat.zero_mul`,
    // `Rat.mul_zero`, `Rat.right_distrib`, `Rat.left_distrib`,
    // `Rat.mul_inv_cancel`) ELIMINATED to genuine quotient
    // `Declaration::Theorem`s over `Rat := Quot Rat.Raw.Equiv`; removed.
    // Fin combinatorial: Fin.castSucc / Fin.last ELIMINATED to Definitions (#3470).
    // Nat bitwise (Nat.shiftLeft ELIMINATED to a Definition #3470; Nat.testBit
    // ELIMINATED to a Definition in Track FF step 1; land/lor/xor ELIMINATED to
    // Definitions `Nat.bitwise and/or/xor` in Track II; shiftRight ELIMINATED to
    // the Definition `fun m n => Nat.iterDiv2 n m` in TCB-shrink Tier-0 — see
    // `algebra_nat_bitwise_def.rs`):
    // (empty — every formerly-admitted Nat/Rat/Fin domain axiom has been
    // discharged to a kernel-checked Definition or Theorem.)
];

/// Returns true if the given name is a genuine Lean 4 *logical-foundation*
/// axiom.
///
/// Genuine foundations (`propext`, `Quot.sound`, `Classical.choice`,
/// `Eq.refl`, `funext`, `proofIrrel`, the `Quot` primitives,
/// `WellFounded.fix`, and the primitive `*.decEq` representation axioms) are
/// part of the Lean 4 logical foundation and are accepted as "constructive".
/// (`Classical.em` / `Classical.byContradiction` are no longer in this set:
/// Diaconescu's theorem demoted them to kernel-checked Theorems whose closures
/// are `⊆ FOUNDATIONAL_AXIOMS` — see `classical_em_proof.rs`.) Admitted DOMAIN
/// axioms
/// (`ADMITTED_DOMAIN_AXIOMS`: the `Rat.*` ordered-field / lattice, `Fin.*`,
/// and `Nat.*` bitwise facts) are NOT foundational — they are unproved-in-Clean
/// domain assumptions, so a theorem reaching one classifies as `AxiomDependent`.
/// Any other axiom is also a domain-specific trust gap.
///
/// Public so downstream pipelines (e.g. `mathverse_shard build-native`) can
/// delegate foundational classification to this single source of truth
/// instead of re-implementing the whitelist.
///
/// **Soundness guard (#3554):** Trust markers (`sorry`, `sorryAx`,
/// `trustedArith`, `trustedAy`) are incomplete-proof / decision-procedure
/// envelopes, NOT foundational axioms. Even if a future edit accidentally
/// re-adds one of them to `FOUNDATIONAL_AXIOMS`, this function short-
/// circuits and returns `false` for every trust-marker name. This
/// belt-and-suspenders guard prevents the pre-#3554 classifier bug (where
/// `sorryAx` was whitelisted as foundational, so theorems transitively
/// reaching `sorry` were reported as `ProofQuality::Constructive`) from
/// ever reappearing via a whitelist regression. The disjointness
/// invariant is additionally pinned by
/// `test_trust_markers_are_disjoint_from_foundational` in
/// `tests_axiom_audit.rs`.
#[must_use]
pub fn is_foundational_axiom(name: &Name) -> bool {
    // Belt-and-suspenders: trust markers are NEVER foundational, regardless
    // of whether the `FOUNDATIONAL_AXIOMS` slice accidentally contains them.
    // See #3554.
    if is_trust_marker(name) {
        return false;
    }
    let s = name.to_string();
    // Admitted domain axioms (Rat ordered-field/lattice, Fin, Nat bitwise) are
    // mathematically true but unproved in THIS kernel, so they are NOT
    // foundational — a theorem reaching one is honestly `AxiomDependent`, not
    // `Constructive`. (Integrity audit 2026-06; reverses the #3490/#3543
    // ergonomic-whitelist overstatement.)
    if ADMITTED_DOMAIN_AXIOMS.iter().any(|&d| s == d) {
        return false;
    }
    FOUNDATIONAL_AXIOMS.iter().any(|&f| s == f)
}

/// Trust markers — names whose transitive presence disqualifies a theorem
/// from `ProofQuality::Constructive`. These are intentionally kept separate
/// from `FOUNDATIONAL_AXIOMS` so that pipelines can distinguish "trust
/// envelope / sorry" from "domain-specific axiom". See #3554.
///
/// | Marker | Source | Meaning |
/// |---|---|---|
/// | `sorry` | `env/core/trust.rs:49` (`init_sorry`) | Deliberate incomplete-proof marker |
/// | `sorryAx` | `env/core/trust.rs:63` (`init_sorry_ax`) | Lean 4–compatible sorry axiom |
/// | `trustedArith` | `env/core/trust.rs:148` (`init_trusted_arith`) | linarith/mathverse solver bridge |
/// | `trustedAy` | `env/core/trust.rs:119` (`init_trusted_ay`) | Ay SMT solver bridge |
///
/// **Soundness note:** Trust markers MUST NOT also appear in
/// `FOUNDATIONAL_AXIOMS`. The pre-#3554 bug was that `sorryAx` was
/// mistakenly whitelisted as foundational, so theorems transitively
/// reaching `sorry` were reported as `ProofQuality::Constructive`. The
/// unit test `test_trust_markers_are_disjoint_from_foundational` pins
/// this invariant.
const TRUST_MARKERS: &[&str] = &["sorry", "sorryAx", "trustedArith", "trustedAy"];

/// Returns true if `name` is a trust-envelope marker (`sorry`, `sorryAx`,
/// `trustedArith`, `trustedAy`). Trust markers are non-foundational by
/// construction — reaching them in the transitive closure should
/// disqualify `ProofQuality::Constructive`.
///
/// Public so downstream pipelines (axiom-audit, mathverse-native shard
/// builder, gamma-crown reports) can distinguish "reached a trust
/// envelope" from "depends on a domain-specific axiom" without
/// re-implementing the whitelist.
///
/// Part of #3554 — the classifier-soundness fix that moved `sorryAx`
/// out of `FOUNDATIONAL_AXIOMS`.
#[must_use]
pub fn is_trust_marker(name: &Name) -> bool {
    let s = name.to_string();
    TRUST_MARKERS.iter().any(|&m| s == m)
}

/// Classification of proof quality for a declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofQuality {
    /// No domain-specific axiom dependencies. Genuinely proved.
    Constructive,
    /// Depends on N domain-specific axioms. Partially proved.
    AxiomDependent {
        /// Number of domain-specific axioms in the transitive closure.
        axiom_count: usize,
        /// Names of those axioms.
        axioms: Vec<Name>,
    },
    /// Not a theorem (axiom or definition).
    NotATheorem,
    /// Uses `add_decl_structural` — not fully kernel-verified.
    Unchecked,
}

/// Whole-environment proof quality summary.
#[derive(Clone, Debug, Default)]
pub struct SoundnessReport {
    /// Total number of declarations in the environment.
    pub total_declarations: usize,
    /// Number of theorems.
    pub theorems: usize,
    /// Number of axioms (including foundational).
    pub axioms: usize,
    /// Number of definitions.
    pub definitions: usize,
    /// Number of opaque constants.
    pub opaques: usize,
    /// Theorems with zero domain-specific axiom dependencies.
    pub constructive_theorems: usize,
    /// Theorems depending on at least one domain-specific axiom.
    pub axiom_dependent_theorems: usize,
    /// Declarations added via `add_decl_structural` (not kernel-verified).
    pub unchecked_declarations: usize,
    /// Total distinct domain-specific axioms across the environment.
    pub total_domain_axioms: usize,
    /// The domain-specific axiom names.
    pub domain_axioms: Vec<Name>,
}

/// A fail-closed problem found while deciding whether a concrete `(goal,
/// term)` pair may carry Clean's strongest certification grade.
///
/// This is intentionally richer than an axiom closure.  A declaration with a
/// proof value can still be uncertified when that value was admitted through a
/// structural/unchecked path, when an imported value has not been rechecked,
/// or when a reachable declaration is unsafe/partial.  Every such state is
/// explicit here rather than being collapsed into an empty closure.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CertificationIssue {
    /// The proposed goal was not itself a well-formed proposition.
    GoalNotProposition { error: String },
    /// The kernel did not accept `term : goal`.
    TermRejected { error: String },
    /// A referenced constant was absent from the environment.
    MissingDeclaration { name: Name },
    /// A reachable non-axiom had no value, so its proof/definition closure was
    /// unavailable (for example after proof-value elision).
    MissingValue { name: Name },
    /// A reachable declaration was inserted via structural validation only.
    StructuralOnly { name: Name },
    /// A reachable declaration was inserted through an unchecked path.
    Unchecked { name: Name },
    /// A structural import is still marked as requiring a genuine recheck.
    NeedsRecheck { name: Name },
    /// A value-less inductive/constructor/recursor object had no transient
    /// record that it passed Clean's inductive checker.  Its metadata may be
    /// internally consistent, but deserialization must not mint authority.
    UnverifiedKernelObject { name: Name },
    /// A reachable declaration is marked unsafe.
    Unsafe { name: Name },
    /// A reachable declaration is marked partial.
    Partial { name: Name },
    /// A reachable incomplete-proof/solver trust marker was found.
    TrustMarker { name: Name },
    /// A reachable axiom is not part of the certification foundation.
    NonFoundationalAxiom { name: Name },
    /// A foundation-shaped name did not exactly match the canonical kind,
    /// universe arity, or statement installed by the kernel.
    NonCanonicalFoundation { name: Name, detail: String },
    /// Re-running the full declaration checker rejected a reachable type/value.
    InvalidDeclaration { name: Name, error: String },
    /// The reachable constant graph contains a cycle.  Fully checked
    /// declarations cannot acquire circular support because `add_decl` checks
    /// before insertion; a cycle therefore exposes unchecked/foreign state.
    DependencyCycle { names: Vec<Name> },
}

/// Expression-rooted certification evidence.
///
/// `dependencies` is the complete, sorted closure reached from both the goal
/// and term, following every constant's type *and* value.  `foundations`
/// contains only exact canonical foundation/kernel-primitive declarations.
/// `rechecked_unknown` makes deserialized/directly-installed declarations
/// visible: missing transient provenance never defaults to checked, but a
/// successful strict read-only recheck can establish the exact declaration
/// for this audit run.  Any entry in `issues` blocks certification.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CertificationAudit {
    /// Complete sorted constant-name closure reached from the goal and term.
    pub dependencies: Vec<Name>,
    /// Exact canonical foundation declarations reached by the proof.
    pub foundations: Vec<Name>,
    /// Declarations with unknown transient provenance that passed a fresh
    /// strict read-only check for this audit run.
    pub rechecked_unknown: Vec<Name>,
    /// Every certification-blocking problem found by the audit.
    pub issues: Vec<CertificationIssue>,
}

impl CertificationAudit {
    /// True only when the root judgment and its entire dependency closure pass
    /// every strict certification check.
    #[must_use]
    pub fn is_certified(&self) -> bool {
        self.issues.is_empty()
    }
}

/// Collect all `Expr::Const` names referenced in an expression tree.
///
/// Walks the expression recursively, collecting every `ExprKind::Const` name.
/// Uses a visited set to avoid reprocessing shared sub-expressions.
fn collect_const_refs(expr: &Expr, out: &mut HashSet<Name>) {
    // Use an explicit stack to avoid deep recursion on large expressions.
    let mut stack: Vec<&Expr> = vec![expr];
    // Expressions are immutable DAGs.  Pointer identity is therefore a safe
    // traversal cache and prevents a shared proof term from expanding
    // exponentially during an authority check.
    let mut visited_nodes: HashSet<usize> = HashSet::new();

    while let Some(e) = stack.pop() {
        if !visited_nodes.insert(e as *const Expr as usize) {
            continue;
        }
        match e.kind() {
            ExprKind::Const(name, _) => {
                out.insert(name.clone());
            }
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::MData(_, inner) => {
                stack.push(inner);
            }
            ExprKind::Proj(struct_name, _, inner) => {
                // Projection reduction consults the named structure metadata;
                // the name is a real dependency even though it is not wrapped
                // in an ExprKind::Const node.
                out.insert(struct_name.clone());
                stack.push(inner);
            }
            ExprKind::Squash(inner) => {
                stack.push(inner);
            }
            ExprKind::CubicalPath { ty, left, right } => {
                stack.push(ty);
                stack.push(left);
                stack.push(right);
            }
            ExprKind::CubicalPathLam { body } => stack.push(body),
            ExprKind::CubicalPathApp { path, arg } => {
                stack.push(path);
                stack.push(arg);
            }
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                stack.push(ty);
                stack.push(phi);
                stack.push(u);
                stack.push(base);
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                stack.push(ty);
                stack.push(phi);
                stack.push(base);
            }
            ExprKind::CubicalCoe { ty, r, s, base } => {
                stack.push(ty);
                stack.push(r);
                stack.push(s);
                stack.push(base);
            }
            ExprKind::ZFCSet(set_expr) => match set_expr {
                crate::expr::ZFCSetExpr::Empty | crate::expr::ZFCSetExpr::Infinity => {}
                crate::expr::ZFCSetExpr::Singleton(a)
                | crate::expr::ZFCSetExpr::Union(a)
                | crate::expr::ZFCSetExpr::PowerSet(a)
                | crate::expr::ZFCSetExpr::Choice(a) => stack.push(a),
                crate::expr::ZFCSetExpr::Pair(a, b)
                | crate::expr::ZFCSetExpr::Separation { set: a, pred: b }
                | crate::expr::ZFCSetExpr::Replacement { set: a, func: b } => {
                    stack.push(a);
                    stack.push(b);
                }
            },
            ExprKind::ZFCMem { element, set } => {
                stack.push(element);
                stack.push(set);
            }
            ExprKind::ZFCComprehension { domain, pred } => {
                stack.push(domain);
                stack.push(pred);
            }
            // Genuine terminals.
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Lit(_)
            | ExprKind::SProp
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1 => {}
        }
    }
}

/// Reconstruct the declaration represented by a stored `ConstantInfo`, so the
/// read-only checker sees exactly the stored type/value pair.
fn declaration_from_info(info: &ConstantInfo) -> Option<Declaration> {
    match info.kind {
        ConstantKind::Definition => Some(Declaration::Definition {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: info.value.clone()?,
            is_reducible: info.is_reducible,
        }),
        ConstantKind::Theorem => Some(Declaration::Theorem {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: info.value.clone()?,
        }),
        ConstantKind::Opaque => Some(Declaration::Opaque {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: info.value.clone()?,
        }),
        ConstantKind::Axiom => Some(Declaration::Axiom {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
        }),
    }
}

fn kernel_generated_metadata_matches(env: &Environment, info: &ConstantInfo) -> bool {
    if info.kind != ConstantKind::Definition || info.value.is_some() {
        return false;
    }
    if let Some(inductive) = env.get_inductive(&info.name) {
        return inductive.level_params == info.level_params && inductive.type_ == info.type_;
    }
    if let Some(constructor) = env.get_constructor(&info.name) {
        return constructor.level_params == info.level_params && constructor.type_ == info.type_;
    }
    if let Some(recursor) = env.get_recursor(&info.name) {
        return recursor.level_params == info.level_params && recursor.type_ == info.type_;
    }
    false
}

fn canonical_propext_type() -> Expr {
    // {a b : Prop} -> Iff a b -> Eq Prop a b
    let iff_ab = Expr::apps(
        Expr::const_(Name::from_string("Iff"), vec![]),
        [Expr::bvar(1), Expr::bvar(0)],
    );
    let eq_ab = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::prop(), Expr::bvar(2), Expr::bvar(1)],
    );
    Expr::pi(
        crate::expr::BinderInfo::Implicit,
        Expr::prop(),
        Expr::pi(
            crate::expr::BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(crate::expr::BinderInfo::Default, iff_ab, eq_ab),
        ),
    )
}

fn canonical_choice_type(u: &Name) -> Expr {
    // {alpha : Sort u} -> Nonempty alpha -> alpha
    let sort_u = Expr::sort(Level::param(u.clone()));
    let nonempty_alpha = Expr::app(
        Expr::const_(Name::from_string("Nonempty"), vec![Level::param(u.clone())]),
        Expr::bvar(0),
    );
    Expr::pi(
        crate::expr::BinderInfo::Implicit,
        sort_u,
        Expr::pi(
            crate::expr::BinderInfo::Default,
            nonempty_alpha,
            Expr::bvar(1),
        ),
    )
}

/// Return the exact canonical declaration signature for an axiom that the
/// certification lane may admit.  The logical foundation is exactly
/// `propext`, `Quot.sound`, and `Classical.choice`; the other four returned
/// objects are Clean's exact quotient kernel primitives, represented as
/// `Axiom`-kind constants but not additional logical assumptions.
fn canonical_certification_foundation(name: &Name) -> Option<(Vec<Name>, Expr)> {
    match name.to_string().as_str() {
        "propext" => Some((Vec::new(), canonical_propext_type())),
        "Classical.choice" => {
            let u = Name::from_string("u");
            Some((vec![u.clone()], canonical_choice_type(&u)))
        }
        _ => crate::quot::init_quot_vals()
            .into_iter()
            .find(|value| value.name == *name)
            .map(|value| (value.level_params, value.type_)),
    }
}

fn canonical_foundation_matches(info: &ConstantInfo) -> Result<(), String> {
    if info.kind != ConstantKind::Axiom {
        return Err(format!("expected Axiom kind, found {:?}", info.kind));
    }
    if info.value.is_some() {
        return Err("canonical foundation must not carry a value".to_string());
    }
    let Some((canonical_params, canonical_type)) = canonical_certification_foundation(&info.name)
    else {
        return Err("name is not in the exact certification foundation".to_string());
    };
    if info.level_params.len() != canonical_params.len() {
        return Err(format!(
            "universe arity {} differs from canonical {}",
            info.level_params.len(),
            canonical_params.len()
        ));
    }
    let normalized_type = if info.level_params == canonical_params {
        info.type_.clone()
    } else {
        let levels: Vec<Level> = canonical_params
            .iter()
            .map(|param| Level::param(param.clone()))
            .collect();
        info.type_
            .instantiate_level_params_direct(&info.level_params, &levels)
    };
    if normalized_type != canonical_type {
        return Err("statement differs from the canonical kernel declaration".to_string());
    }
    Ok(())
}

fn cycle_candidates(graph: &BTreeMap<Name, BTreeSet<Name>>) -> Vec<Name> {
    let mut indegree: BTreeMap<Name, usize> = graph.keys().cloned().map(|name| (name, 0)).collect();
    for targets in graph.values() {
        for target in targets {
            if let Some(degree) = indegree.get_mut(target) {
                *degree += 1;
            }
        }
    }

    // Kahn over source -> dependency edges.  Remaining nodes contain every
    // cycle (and, conservatively, nodes downstream of one); any remainder is
    // enough to reject circular proof support.
    let mut queue: VecDeque<Name> = indegree
        .iter()
        .filter(|(_, degree)| **degree == 0)
        .map(|(name, _)| name.clone())
        .collect();
    while let Some(source) = queue.pop_front() {
        let Some(targets) = graph.get(&source) else {
            continue;
        };
        for target in targets {
            if let Some(degree) = indegree.get_mut(target) {
                *degree = degree.saturating_sub(1);
                if *degree == 0 {
                    queue.push_back(target.clone());
                }
            }
        }
    }
    indegree
        .into_iter()
        .filter(|(_, degree)| *degree > 0)
        .map(|(name, _)| name)
        .collect()
}

impl Environment {
    /// Strictly audit one concrete proof judgment for certification authority.
    ///
    /// Unlike the legacy `axiom_deps(name)` pattern, this starts directly from
    /// both expressions and never registers a fixed synthetic theorem in a
    /// cloned environment.  It walks the unfiltered type/value dependency
    /// closure, re-runs the full declaration checker on every reachable stored
    /// declaration, validates admitted foundations by exact canonical
    /// statement (not name), and exposes every provenance/trust hazard.
    ///
    /// The method is read-only and deterministic.  An empty issue list is the
    /// only certification-success state.
    #[must_use]
    pub fn audit_certification(&self, goal: &Expr, term: &Expr) -> CertificationAudit {
        let mut audit = CertificationAudit::default();

        let mut tc = crate::tc::TypeChecker::new(self);
        tc.set_allow_unsafe(false);
        tc.set_allow_partial(false);
        match tc.infer_sort(goal) {
            Ok(sort) if sort.is_zero() => {}
            Ok(sort) => audit.issues.push(CertificationIssue::GoalNotProposition {
                error: format!("goal lives in Sort {sort:?}, not Prop"),
            }),
            Err(error) => audit.issues.push(CertificationIssue::GoalNotProposition {
                error: format!("{error:?}"),
            }),
        }
        if let Err(error) = tc.check_type(term, goal) {
            audit.issues.push(CertificationIssue::TermRejected {
                error: format!("{error:?}"),
            });
        }

        let mut root_refs = HashSet::new();
        collect_const_refs(goal, &mut root_refs);
        collect_const_refs(term, &mut root_refs);
        let mut pending: BTreeSet<Name> = root_refs.into_iter().collect();
        let mut dependencies = BTreeSet::new();
        let mut foundations = BTreeSet::new();
        let mut rechecked_unknown = BTreeSet::new();
        let mut graph: BTreeMap<Name, BTreeSet<Name>> = BTreeMap::new();

        while let Some(name) = pending.pop_first() {
            if !dependencies.insert(name.clone()) {
                continue;
            }
            let Some(info) = self.get_const(&name) else {
                audit
                    .issues
                    .push(CertificationIssue::MissingDeclaration { name });
                continue;
            };

            if self.is_unsafe(&name) {
                audit
                    .issues
                    .push(CertificationIssue::Unsafe { name: name.clone() });
            }
            if self.is_partial(&name) {
                audit
                    .issues
                    .push(CertificationIssue::Partial { name: name.clone() });
            }
            if is_trust_marker(&name) {
                audit
                    .issues
                    .push(CertificationIssue::TrustMarker { name: name.clone() });
            }
            if self.constant_needs_recheck(&name) {
                audit
                    .issues
                    .push(CertificationIssue::NeedsRecheck { name: name.clone() });
            }

            match self.declaration_verification(&name) {
                Some(DeclarationVerification::FullKernelCheck) => {}
                Some(DeclarationVerification::StructuralOnly) => audit
                    .issues
                    .push(CertificationIssue::StructuralOnly { name: name.clone() }),
                Some(DeclarationVerification::Unchecked) => audit
                    .issues
                    .push(CertificationIssue::Unchecked { name: name.clone() }),
                None => {
                    // Unknown is never silently promoted.  It is listed in the
                    // report and accepted for this run only if the strict
                    // declaration recheck below succeeds and no other issue is
                    // found.  Structural imports additionally carry
                    // `NeedsRecheck`, which remains blocking.
                    rechecked_unknown.insert(name.clone());
                }
            }

            if info.kind == ConstantKind::Axiom {
                if canonical_certification_foundation(&name).is_some() {
                    match canonical_foundation_matches(info) {
                        Ok(()) => {
                            foundations.insert(name.clone());
                        }
                        Err(detail) => {
                            audit
                                .issues
                                .push(CertificationIssue::NonCanonicalFoundation {
                                    name: name.clone(),
                                    detail,
                                })
                        }
                    }
                } else if is_foundational_axiom(&name) {
                    // The historical broad name whitelist is not authority.
                    // A name without an exact canonical signature is visible
                    // and rejected instead of disappearing from the closure.
                    audit
                        .issues
                        .push(CertificationIssue::NonCanonicalFoundation {
                            name: name.clone(),
                            detail:
                                "foundational name has no exact canonical certification declaration"
                                    .to_string(),
                        });
                } else if !is_trust_marker(&name) {
                    audit
                        .issues
                        .push(CertificationIssue::NonFoundationalAxiom { name: name.clone() });
                }
            }

            let Some(decl) = declaration_from_info(info) else {
                if kernel_generated_metadata_matches(self, info) {
                    // Inductive heads, constructors, and primitive recursors
                    // intentionally have no ordinary value: their computation
                    // rules live in kernel metadata.  Exact cross-table
                    // agreement plus a well-formed type is necessary, and a
                    // transient FullKernelCheck stamp proves this instance came
                    // through add_inductive rather than deserialization/import.
                    let type_decl = Declaration::Axiom {
                        name: name.clone(),
                        level_params: info.level_params.clone(),
                        type_: info.type_.clone(),
                    };
                    if let Err(error) = self.check_decl_readonly_strict(&type_decl) {
                        audit.issues.push(CertificationIssue::InvalidDeclaration {
                            name: name.clone(),
                            error: error.to_string(),
                        });
                    }
                    if self.declaration_verification(&name)
                        != Some(DeclarationVerification::FullKernelCheck)
                    {
                        audit
                            .issues
                            .push(CertificationIssue::UnverifiedKernelObject {
                                name: name.clone(),
                            });
                    }
                    let mut refs = HashSet::new();
                    collect_const_refs(&info.type_, &mut refs);
                    let refs: BTreeSet<Name> = refs.into_iter().collect();
                    pending.extend(refs.iter().cloned());
                    graph.insert(name, refs);
                } else {
                    audit
                        .issues
                        .push(CertificationIssue::MissingValue { name: name.clone() });
                    graph.entry(name).or_default();
                }
                continue;
            };
            if let Err(error) = self.check_decl_readonly_strict(&decl) {
                audit.issues.push(CertificationIssue::InvalidDeclaration {
                    name: name.clone(),
                    error: error.to_string(),
                });
            }

            let mut refs = HashSet::new();
            collect_const_refs(&info.type_, &mut refs);
            if let Some(value) = &info.value {
                collect_const_refs(value, &mut refs);
            }
            let refs: BTreeSet<Name> = refs.into_iter().collect();
            pending.extend(refs.iter().cloned());
            graph.insert(name, refs);
        }

        let cycle = cycle_candidates(&graph);
        if !cycle.is_empty() {
            audit
                .issues
                .push(CertificationIssue::DependencyCycle { names: cycle });
        }

        audit.dependencies = dependencies.into_iter().collect();
        audit.foundations = foundations.into_iter().collect();
        audit.rechecked_unknown = rechecked_unknown.into_iter().collect();
        audit
    }

    /// Returns the set of all non-foundational axioms in the transitive
    /// dependency tree of the given declaration.
    ///
    /// **Algorithm:**
    /// 1. Start from the declaration's proof term (if Theorem) or type (if Axiom/Definition)
    /// 2. Walk the `Expr` tree, collecting all `Expr::Const` references
    /// 3. For each referenced constant that is an `Axiom` in the environment,
    ///    check if it is foundational; if not, add it to the result
    /// 4. Recursively walk that axiom's type for more transitive dependencies
    /// 5. Return the set of domain-specific axioms
    ///
    /// Trust markers (`sorry`, `sorryAx`, `trustedArith`, `trustedAy`) are
    /// **not foundational** — they appear in the returned set and therefore
    /// disqualify a theorem from `ProofQuality::Constructive` (see #3554).
    /// Callers that want to distinguish "reached sorry" from "reached a
    /// domain axiom" should compare against
    /// [`Environment::trust_marker_deps`].
    ///
    /// Returns `None` if the declaration is not found.
    pub fn axiom_deps(&self, name: &Name) -> Option<HashSet<Name>> {
        let info = self.get_const(name)?;

        // Collect all constants referenced in the declaration
        let mut all_const_refs = HashSet::new();
        collect_const_refs(&info.type_, &mut all_const_refs);
        if let Some(ref value) = info.value {
            collect_const_refs(value, &mut all_const_refs);
        }

        // BFS/DFS through transitive axiom dependencies
        let mut domain_axioms = HashSet::new();
        let mut visited = HashSet::new();
        visited.insert(name.clone());
        let mut worklist: Vec<Name> = all_const_refs.into_iter().collect();

        while let Some(ref_name) = worklist.pop() {
            if !visited.insert(ref_name.clone()) {
                continue;
            }

            if let Some(ref_info) = self.get_const(&ref_name) {
                // Trust markers AND domain-specific axioms both land in the
                // deps set. Only foundational axioms (propext, Quot.sound,
                // Eq.*, etc.) are filtered out. Reaching `sorryAx` / `sorry`
                // / `trustedArith` / `trustedAy` in the transitive closure
                // disqualifies `ProofQuality::Constructive` (#3554).
                if ref_info.kind == ConstantKind::Axiom && !is_foundational_axiom(&ref_name) {
                    domain_axioms.insert(ref_name.clone());
                }

                // Walk the type of every referenced constant (axiom or not)
                // to find transitive axiom dependencies
                let mut transitive_refs = HashSet::new();
                collect_const_refs(&ref_info.type_, &mut transitive_refs);
                if let Some(ref value) = ref_info.value {
                    collect_const_refs(value, &mut transitive_refs);
                }
                for tr in transitive_refs {
                    if !visited.contains(&tr) {
                        worklist.push(tr);
                    }
                }
            }
        }

        Some(domain_axioms)
    }

    /// Returns the subset of [`Environment::axiom_deps`] that are **trust
    /// markers** (`sorry`, `sorryAx`, `trustedArith`, `trustedAy`).
    ///
    /// Trust markers indicate a proof reached an incomplete-proof sentinel
    /// (`sorry` / `sorryAx`) or a decision-procedure bridge (`trustedArith`
    /// / `trustedAy`) rather than a kernel proof. Callers that want to
    /// distinguish "reached sorry" from "depends on a domain-specific
    /// axiom" should diff this set against [`Environment::axiom_deps`]:
    ///
    /// ```text
    /// let all_deps = env.axiom_deps(&name)?;
    /// let trust = env.trust_marker_deps(&name)?;
    /// let domain_only: HashSet<_> = all_deps.difference(&trust).cloned().collect();
    /// ```
    ///
    /// Returns `None` if the declaration is not found. Part of #3554.
    pub fn trust_marker_deps(&self, name: &Name) -> Option<HashSet<Name>> {
        let deps = self.axiom_deps(name)?;
        Some(deps.into_iter().filter(is_trust_marker).collect())
    }

    /// Classify the proof quality of a declaration.
    ///
    /// - `Constructive`: theorem with zero domain-specific axiom dependencies
    /// - `AxiomDependent`: theorem that transitively depends on domain-specific axioms
    /// - `NotATheorem`: axiom, definition, or opaque constant
    /// - `Unchecked`: a `Theorem`-kind constant whose stored `value` is `None`
    ///   (i.e. a proof-less theorem)
    ///
    /// This classifier keys off two observable facts only — whether the
    /// constant carries a proof `value`, and what its transitive axiom
    /// closure contains. It does NOT, on its own, detect a theorem that was
    /// added structurally (via `add_decl_structural`) and therefore skipped
    /// full kernel type-checking: such theorems still carry their proof
    /// `value`, so they fall through to the value-present branch below and are
    /// classified as `Constructive` / `AxiomDependent` by their axiom closure,
    /// exactly like fully kernel-checked theorems. Distinguishing
    /// "structurally added but not kernel-verified" requires separate
    /// provenance tracking, not this function.
    ///
    /// Returns `None` if the declaration is not found.
    pub fn proof_quality(&self, name: &Name) -> Option<ProofQuality> {
        let info = self.get_const(name)?;

        // Only theorems can be Constructive or AxiomDependent
        if info.kind != ConstantKind::Theorem {
            return Some(ProofQuality::NotATheorem);
        }

        // A `Theorem`-kind constant with no stored proof value: classify as
        // `Unchecked`. Note this only fires on `value.is_none()`; a theorem
        // added via `add_decl_structural` still carries its proof `value`
        // (see `add_decl_structural`'s `Declaration::Theorem` arm, which
        // stores `Some(value)`), so a structurally-added-but-unverified
        // theorem does NOT reach this branch — it is classified below by its
        // axiom closure.
        if info.value.is_none() {
            return Some(ProofQuality::Unchecked);
        }

        let deps = self.axiom_deps(name)?;
        if deps.is_empty() {
            Some(ProofQuality::Constructive)
        } else {
            let mut axioms: Vec<Name> = deps.into_iter().collect();
            axioms.sort_by_key(|a| a.to_string());
            Some(ProofQuality::AxiomDependent {
                axiom_count: axioms.len(),
                axioms,
            })
        }
    }

    /// Produce a whole-environment proof quality summary.
    ///
    /// Walks ALL declarations and classifies each one.
    pub fn soundness_report(&self) -> SoundnessReport {
        let mut report = SoundnessReport::default();
        let mut all_domain_axioms = HashSet::new();

        // Collect all constants into a vec to avoid borrow issues
        let const_names: Vec<(Name, ConstantKind)> =
            self.constants().map(|c| (c.name.clone(), c.kind)).collect();

        report.total_declarations = const_names.len();

        for (name, kind) in &const_names {
            match kind {
                ConstantKind::Theorem => {
                    report.theorems += 1;
                    match self.proof_quality(name) {
                        Some(ProofQuality::Constructive) => {
                            report.constructive_theorems += 1;
                        }
                        Some(ProofQuality::AxiomDependent { axioms, .. }) => {
                            report.axiom_dependent_theorems += 1;
                            for ax in &axioms {
                                all_domain_axioms.insert(ax.clone());
                            }
                        }
                        Some(ProofQuality::Unchecked) => {
                            report.unchecked_declarations += 1;
                        }
                        _ => {}
                    }
                }
                ConstantKind::Axiom => {
                    report.axioms += 1;
                    if !is_foundational_axiom(name) {
                        all_domain_axioms.insert(name.clone());
                    }
                }
                ConstantKind::Definition => {
                    report.definitions += 1;
                }
                ConstantKind::Opaque => {
                    report.opaques += 1;
                }
            }
        }

        let mut domain_axioms: Vec<Name> = all_domain_axioms.into_iter().collect();
        domain_axioms.sort_by_key(|a| a.to_string());
        report.total_domain_axioms = domain_axioms.len();
        report.domain_axioms = domain_axioms;

        report
    }
}

#[cfg(test)]
mod certification_tests {
    use super::*;

    fn true_env() -> Environment {
        let mut env = Environment::new();
        env.init_true_false().expect("initialize True/False");
        env
    }

    fn true_goal() -> Expr {
        Expr::const_(Name::from_string("True"), vec![])
    }

    fn true_intro() -> Expr {
        Expr::const_(Name::from_string("True.intro"), vec![])
    }

    #[test]
    fn certification_audit_accepts_a_clean_kernel_proof() {
        let env = true_env();
        let audit = env.audit_certification(&true_goal(), &true_intro());
        assert!(audit.is_certified(), "audit: {audit:#?}");
        assert!(audit
            .dependencies
            .contains(&Name::from_string("True.intro")));
    }

    #[test]
    fn certification_audit_accepts_prelude_equality_reflexivity() {
        let env = Environment::with_prelude();
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let one = Expr::nat_lit(1);
        let goal = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat.clone(), one.clone(), one.clone()],
        );
        let term = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [nat, one],
        );
        let audit = env.audit_certification(&goal, &term);
        assert!(audit.is_certified(), "audit: {audit:#?}");
    }

    #[test]
    fn repaired_eq_recursors_reearn_full_current_payload_authority() {
        let env = Environment::with_prelude();
        for recursor in ["Eq.rec", "Eq.casesOn", "Eq.recOn"] {
            let name = Name::from_string(recursor);
            assert_eq!(
                env.declaration_verification(&name),
                Some(DeclarationVerification::FullKernelCheck),
                "{recursor} must be stamped only after its repaired payload"
            );
            env.validate_recursor_metadata(&name)
                .unwrap_or_else(|error| panic!("{recursor}: {error}"));
        }
    }

    fn assert_no_confusion_pair_is_rooted(env: &Environment, inductive: &str) {
        let type_name = Name::from_string(&format!("{inductive}.noConfusionType"));
        let theorem_name = Name::from_string(&format!("{inductive}.noConfusion"));
        for name in [&type_name, &theorem_name] {
            assert_eq!(
                env.declaration_verification(name),
                Some(DeclarationVerification::FullKernelCheck),
                "{name} must earn full provenance from its current exact payload"
            );
        }

        // Instantiate the result universe at Prop so the generated eliminator
        // itself is a closed certification judgment. This exercises the full
        // rooted closure, not merely the transient provenance table.
        let info = env
            .get_const(&theorem_name)
            .unwrap_or_else(|| panic!("missing {theorem_name}"));
        let levels = vec![Level::zero(); info.level_params.len()];
        let goal = info
            .type_
            .instantiate_level_params_direct(&info.level_params, &levels);
        let term = Expr::const_(theorem_name, levels);
        let audit = env.audit_certification(&goal, &term);
        assert!(
            audit.is_certified(),
            "{inductive}.noConfusion must pass the complete rooted audit: {audit:#?}"
        );
    }

    #[test]
    fn late_equality_rechecks_generated_no_confusion_pairs() {
        let mut env = Environment::new();
        env.init_nat().expect("initialize Nat before Eq");
        env.init_bool().expect("initialize Bool before Eq");
        env.init_int().expect("initialize Int before Eq");

        for inductive in ["Nat", "Bool", "Int"] {
            let theorem = Name::from_string(&format!("{inductive}.noConfusion"));
            assert!(
                env.get_const(&theorem).is_none(),
                "the pre-Eq fail-closed state must leave {theorem} absent"
            );
            assert_eq!(env.declaration_verification(&theorem), None);
        }

        env.init_eq().expect("initialize Eq and retry exact pairs");
        for inductive in ["Nat", "Bool", "Int"] {
            assert_no_confusion_pair_is_rooted(&env, inductive);
        }
    }

    #[test]
    fn prelude_core_no_confusion_pairs_are_rooted() {
        let env = Environment::with_prelude();
        for inductive in ["Nat", "Bool", "Int"] {
            assert_no_confusion_pair_is_rooted(&env, inductive);
        }
    }

    #[test]
    fn certification_audit_rejects_structural_self_support() {
        let mut env = true_env();
        let evil = Name::from_string("evil");
        env.add_decl_structural(Declaration::Theorem {
            name: evil.clone(),
            level_params: vec![],
            type_: true_goal(),
            value: Expr::const_(evil.clone(), vec![]),
        })
        .expect("structural lane admits circular fixture");

        let audit = env.audit_certification(&true_goal(), &Expr::const_(evil.clone(), vec![]));
        assert!(!audit.is_certified(), "circular structural proof must fail");
        assert!(audit.issues.iter().any(
            |issue| matches!(issue, CertificationIssue::StructuralOnly { name } if name == &evil)
        ));
        assert!(audit
            .issues
            .iter()
            .any(|issue| matches!(issue, CertificationIssue::DependencyCycle { names } if names.contains(&evil))));
    }

    #[test]
    fn certification_audit_rechecks_and_rejects_structural_bad_value() {
        let mut env = true_env();
        let evil = Name::from_string("badValue");
        env.add_decl_structural(Declaration::Theorem {
            name: evil.clone(),
            level_params: vec![],
            type_: true_goal(),
            // `Prop : Sort 1`, not a proof of True.
            value: Expr::prop(),
        })
        .expect("structural lane admits ill-typed fixture");

        let audit = env.audit_certification(&true_goal(), &Expr::const_(evil.clone(), vec![]));
        assert!(audit.issues.iter().any(
            |issue| matches!(issue, CertificationIssue::InvalidDeclaration { name, .. } if name == &evil)
        ));
    }

    #[test]
    fn certification_foundation_is_statement_exact_not_name_only() {
        let mut env = true_env();
        let fake = Name::from_string("propext");
        env.add_decl(Declaration::Axiom {
            name: fake.clone(),
            level_params: vec![],
            // This is a perfectly well-formed axiom declaration, but not the
            // canonical propext statement.
            type_: true_goal(),
        })
        .expect("well-formed fake foundation fixture");

        let audit = env.audit_certification(&true_goal(), &Expr::const_(fake.clone(), vec![]));
        assert!(audit.issues.iter().any(|issue| matches!(
            issue,
            CertificationIssue::NonCanonicalFoundation { name, .. } if name == &fake
        )));
    }

    #[test]
    fn certification_rejects_legacy_proof_irrel_name_spoof() {
        let mut env = true_env();
        let fake = Name::from_string("proofIrrel");
        env.add_decl(Declaration::Axiom {
            name: fake.clone(),
            level_params: vec![],
            type_: true_goal(),
        })
        .expect("well-formed legacy foundation-name fixture");

        let audit = env.audit_certification(&true_goal(), &Expr::const_(fake.clone(), vec![]));
        assert!(audit.issues.iter().any(|issue| matches!(
            issue,
            CertificationIssue::NonCanonicalFoundation { name, .. } if name == &fake
        )));
    }

    #[test]
    fn canonical_live_foundations_match_exact_signatures() {
        let env = Environment::with_prelude();
        for name in ["propext", "Quot.sound", "Classical.choice"] {
            let name = Name::from_string(name);
            let info = env.get_const(&name).expect("live foundation");
            canonical_foundation_matches(info)
                .unwrap_or_else(|error| panic!("{name} is not canonical: {error}"));
        }
    }

    #[test]
    fn certification_audit_exposes_unsafe_and_partial_dependencies() {
        let mut env = true_env();
        let unsafe_name = Name::from_string("unsafeProof");
        let partial_name = Name::from_string("partialProof");
        for name in [&unsafe_name, &partial_name] {
            env.add_decl(Declaration::Theorem {
                name: name.clone(),
                level_params: vec![],
                type_: true_goal(),
                value: true_intro(),
            })
            .expect("checked proof fixture");
        }
        env.mark_unsafe(unsafe_name.clone());
        env.mark_partial(partial_name.clone());

        let unsafe_audit =
            env.audit_certification(&true_goal(), &Expr::const_(unsafe_name.clone(), vec![]));
        assert!(unsafe_audit.issues.iter().any(
            |issue| matches!(issue, CertificationIssue::Unsafe { name } if name == &unsafe_name)
        ));
        let partial_audit =
            env.audit_certification(&true_goal(), &Expr::const_(partial_name.clone(), vec![]));
        assert!(partial_audit.issues.iter().any(
            |issue| matches!(issue, CertificationIssue::Partial { name } if name == &partial_name)
        ));
    }

    #[test]
    fn certification_audit_exposes_missing_and_trust_marker_dependencies() {
        let mut env = true_env();
        let missing = Name::from_string("missingProof");
        let wrapper = Name::from_string("missingWrapper");
        env.add_decl_structural(Declaration::Theorem {
            name: wrapper.clone(),
            level_params: vec![],
            type_: true_goal(),
            value: Expr::const_(missing.clone(), vec![]),
        })
        .expect("structural missing fixture");
        let missing_audit = env.audit_certification(&true_goal(), &Expr::const_(wrapper, vec![]));
        assert!(missing_audit.issues.iter().any(
            |issue| matches!(issue, CertificationIssue::MissingDeclaration { name } if name == &missing)
        ));

        let sorry = Expr::app(
            Expr::const_(Name::from_string("sorry"), vec![Level::zero()]),
            true_goal(),
        );
        let sorry_audit = env.audit_certification(&true_goal(), &sorry);
        assert!(sorry_audit.issues.iter().any(|issue| matches!(
            issue,
            CertificationIssue::TrustMarker { name } if name == &Name::from_string("sorry")
        )));
    }

    #[test]
    fn serialized_provenance_is_unknown_and_rechecked_never_default_trusted() {
        let mut env = Environment::new();
        let theorem = Name::from_string("closedId");
        let goal = Expr::pi(
            crate::expr::BinderInfo::Default,
            Expr::prop(),
            Expr::pi(
                crate::expr::BinderInfo::Default,
                Expr::bvar(0),
                Expr::bvar(1),
            ),
        );
        let value = Expr::lam(
            crate::expr::BinderInfo::Default,
            Expr::prop(),
            Expr::lam(
                crate::expr::BinderInfo::Default,
                Expr::bvar(0),
                Expr::bvar(0),
            ),
        );
        env.add_decl(Declaration::Theorem {
            name: theorem.clone(),
            level_params: vec![],
            type_: goal.clone(),
            value,
        })
        .expect("closed theorem");
        let encoded = env.to_bincode().expect("serialize env");
        let loaded = Environment::from_bincode(&encoded).expect("deserialize env");
        assert_eq!(loaded.declaration_verification(&theorem), None);
        let audit = loaded.audit_certification(&goal, &Expr::const_(theorem.clone(), vec![]));
        assert!(
            audit.is_certified(),
            "strict recheck should recover: {audit:#?}"
        );
        assert!(audit.rechecked_unknown.contains(&theorem));
    }

    #[test]
    fn removing_or_eliding_a_declaration_clears_its_verification_stamp() {
        let mut env = Environment::new();
        let theorem = Name::from_string("ephemeralProof");
        env.add_decl(Declaration::Opaque {
            name: theorem.clone(),
            level_params: vec![],
            type_: Expr::pi(crate::expr::BinderInfo::Default, Expr::prop(), Expr::prop()),
            value: Expr::lam(
                crate::expr::BinderInfo::Default,
                Expr::prop(),
                Expr::bvar(0),
            ),
        })
        .expect("checked opaque fixture");
        assert_eq!(
            env.declaration_verification(&theorem),
            Some(DeclarationVerification::FullKernelCheck)
        );

        assert!(env.forget_value(&theorem));
        assert_eq!(env.declaration_verification(&theorem), None);
        assert!(env.forget_decl(&theorem));
        assert_eq!(env.declaration_verification(&theorem), None);
    }

    #[test]
    fn imported_stub_replacement_cannot_inherit_a_full_stamp() {
        let mut env = true_env();
        let name = Name::from_string("privateStub");
        env.add_decl(Declaration::Axiom {
            name: name.clone(),
            level_params: vec![],
            type_: true_goal(),
        })
        .expect("checked stub");
        assert_eq!(
            env.declaration_verification(&name),
            Some(DeclarationVerification::FullKernelCheck)
        );

        let replacement =
            ConstantInfo::new(name.clone(), vec![], true_goal(), Some(true_intro()), true);
        assert_eq!(env.upgrade_axiom_stubs(std::iter::once(replacement)), 1);
        assert_eq!(
            env.declaration_verification(&name),
            Some(DeclarationVerification::Unchecked)
        );

        let audit = env.audit_certification(&true_goal(), &Expr::const_(name.clone(), vec![]));
        assert!(audit.issues.iter().any(
            |issue| matches!(issue, CertificationIssue::Unchecked { name: found } if found == &name)
        ));
    }
}

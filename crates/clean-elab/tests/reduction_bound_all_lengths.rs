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
//! - the DEFINITIONS those statements are written in mean what they meant when
//!   the pins were taken, so a definition changed under an unchanged statement
//!   text fails the test. Two pins, both required:
//!   * `DEFINITION_PINS` restates every definition as an equation proved by
//!     `rfl`: each format's `emax`, `nmin` and largest finite value, the two
//!     rounding functions, the two underflow modes, contraction, and the
//!     evaluation of a schedule (its bracketing is the tree, its order the
//!     permutation `List.Perm` of its operands). This is the readable pin: it
//!     says what each definition is;
//!   * `DEFINITION_DIGESTS` pins the kernel's closure digest
//!     (`Environment::closure_digest`: SHA-256 over every kernel record the
//!     name reaches, the prelude's included) of each of them. This is the
//!     complete pin: nothing a definition reaches can change unnoticed;
//!   * and the two lists are complete for the statements: every constant a
//!     headline statement or a witness predicate mentions is in the closure of
//!     a digested name or is one of `RESTATED_ONLY` (asserted below), so a
//!     definition the statements come to use cannot stay outside the pins;
//! - the bounds are not vacuous and not loose: for each theorem (sum, dot
//!   product not fused, dot product fused), each format, each rounding and each
//!   underflow mode there is a kernel-checked witness (`witnesses`) in which the
//!   theorem's hypotheses hold, the error is not zero, and
//!   `error >= bound / c` for the factor `c` the table states (a checked
//!   inequality `cd * bound <= cn * error` with `c = cn / cd`);
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
//!
//! # When a definition digest moves
//!
//! The failure names the definitions that moved and prints the table to paste.
//! Before pasting it, read the diff of `proofs/reduction_bound.lean` and of the
//! prelude: a digest moves when a definition, or anything it reaches, changed
//! in the kernel's records. If the meaning changed, the restated equation in
//! `DEFINITION_PINS` changes with it, in the same commit, and
//! docs/DECISIONS.md (the reduction-bound section) says why. If the equations
//! still hold and no definition's source changed, the elaborator or the prelude
//! encodes the same definitions differently, and the table is pasted as it is.
//! A digest does not depend on comments, on blank lines, or on where in the
//! file a declaration stands.

use std::collections::{BTreeSet, HashSet};
use std::fmt::Write as _;

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
const CORE: [&str; 17] = [
    "ReductionBound.sched_bound",
    "ReductionBound.sum_bound",
    "ReductionBound.sum_bound_n",
    "ReductionBound.dot_bound",
    "ReductionBound.dot_bound_n",
    "ReductionBound.device_sum_bound",
    "ReductionBound.device_dot_bound",
    "ReductionBound.Device.rel_or_abs",
    "ReductionBound.leftTree_attains",
    // A kernel computation with `pw` in place of `2 ^ .` is a fact about `eval`.
    "ReductionBound.pw_eq",
    "ReductionBound.pw_fun",
    "ReductionBound.evalP_pow",
    "ReductionBound.eval_of_pw",
    // A witness is an instance of the headline theorem: its hypotheses are the
    // theorem's, and its error lies between `bound / c` and the bound.
    "ReductionBound.sumAttained_headline_binary32",
    "ReductionBound.sumAttained_headline_binary64",
    "ReductionBound.dotAttained_headline_binary32",
    "ReductionBound.dotAttained_headline_binary64",
];

/// Definition pins, restated. Each theorem writes a definition out in full and
/// is proved by `rfl`, so it holds exactly while the definition unfolds to the
/// text here. Read with the headline pins above: the statements are written in
/// these definitions, in the prelude's list length and list membership
/// (restated at the end), and in the prelude's logic and arithmetic of natural
/// numbers, which the digests reach. The test asserts that this is all.
const DEFINITION_PINS: &str = r#"
namespace ReductionBoundDefPins
open ReductionBound

-- Exact integers.
theorem def_adiff (x y : Nat) : adiff x y = (x - y) + (y - x) := rfl
theorem def_Z (p n : Nat) : (Z.mk p n).pos = p ∧ (Z.mk p n).neg = n := ⟨rfl, rfl⟩
theorem def_Z_zero : Z.zero = ⟨0, 0⟩ := rfl
theorem def_Z_add (a b : Z) : Z.add a b = ⟨a.pos + b.pos, a.neg + b.neg⟩ := rfl
theorem def_Z_mul (a b : Z) :
    Z.mul a b = ⟨a.pos * b.pos + a.neg * b.neg, a.pos * b.neg + a.neg * b.pos⟩ := rfl
theorem def_Z_mag (a : Z) : Z.mag a = adiff a.pos a.neg := rfl
theorem def_Z_dist (a b : Z) : Z.dist a b = adiff (a.pos + b.neg) (a.neg + b.pos) := rfl

-- Formats: precision p = t + 1, emin = -eminNeg, emax; K = p - 1 - emin; values in base
-- units 2^(-2K).
theorem def_Format (t e m : Nat) :
    (Format.mk t e m).t = t ∧ (Format.mk t e m).eminNeg = e ∧ (Format.mk t e m).emax = m :=
  ⟨rfl, rfl, rfl⟩
theorem def_Format_K (f : Format) : f.K = f.t + f.eminNeg := rfl
theorem def_Format_E (f : Format) : f.E = f.emax + f.eminNeg := rfl
theorem def_Format_nmin (f : Format) : f.nmin = 2 ^ (f.t + f.K) := rfl
theorem def_Format_maxF (f : Format) : f.maxF = (2 ^ (f.t + 1) - 1) * 2 ^ (f.K + f.E) := rfl
theorem def_binary32 : binary32 = ⟨23, 126, 127⟩ := rfl
theorem def_binary64 : binary64 = ⟨52, 1022, 1023⟩ := rfl
-- IEEE 754 binary32: p = 24, emin = -126, emax = 127; nmin = 2^-126 and the largest finite
-- (2 - 2^-23) 2^127, in base units 2^-298.
theorem val_binary32 : binary32.t + 1 = 24 ∧ binary32.eminNeg = 126 ∧ binary32.emax = 127 ∧
    binary32.K = 149 ∧ binary32.nmin = 2 ^ 172 ∧ binary32.maxF = (2 ^ 24 - 1) * 2 ^ 402 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
-- IEEE 754 binary64: p = 53, emin = -1022, emax = 1023; nmin = 2^-1022 and the largest finite
-- (2 - 2^-52) 2^1023, in base units 2^-2148.
theorem val_binary64 : binary64.t + 1 = 53 ∧ binary64.eminNeg = 1022 ∧ binary64.emax = 1023 ∧
    binary64.K = 1074 ∧ binary64.nmin = 2 ^ 1126 ∧ binary64.maxF = (2 ^ 53 - 1) * 2 ^ 3119 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Rounding and underflow modes: exactly these.
theorem def_Rounding (r : Rounding) : r = .nearestEven ∨ r = .towardZero := by
  cases r with
  | nearestEven => exact Or.inl rfl
  | towardZero => exact Or.inr rfl
theorem def_Underflow (u : Underflow) : u = .gradual ∨ u = .flush := by
  cases u with
  | gradual => exact Or.inl rfl
  | flush => exact Or.inr rfl

-- The rounding functions.
theorem def_expSearch_zero (p n e : Nat) : expSearch p n 0 e = e := rfl
theorem def_expSearch_succ (p n f e : Nat) : expSearch p n (f + 1) e =
    (if Nat.blt n (2 ^ (p + e)) = true then e else expSearch p n f (e + 1)) := rfl
theorem def_Format_expo (f : Format) (n : Nat) : f.expo n = expSearch (f.t + 1) n n f.K := rfl
theorem def_rndAt_towardZero (e n : Nat) : rndAt .towardZero e n = n / 2 ^ e * 2 ^ e := rfl
theorem def_rndAt_nearestEven (e n : Nat) : rndAt .nearestEven e n =
    (if Nat.blt (2 ^ e) (2 * (n % 2 ^ e)) = true then (n / 2 ^ e + 1) * 2 ^ e
     else if Nat.beq (2 * (n % 2 ^ e)) (2 ^ e) = true then
       (if Nat.beq (n / 2 ^ e % 2) 1 = true then (n / 2 ^ e + 1) * 2 ^ e else n / 2 ^ e * 2 ^ e)
     else n / 2 ^ e * 2 ^ e) := rfl
theorem def_Format_rndMag (f : Format) (r : Rounding) (n : Nat) :
    f.rndMag r n = rndAt r (f.expo n) n := rfl
theorem def_Format_roundG (f : Format) (r : Rounding) (z : Z) : f.roundG r z =
    (if Nat.ble z.neg z.pos = true then (⟨f.rndMag r (z.pos - z.neg), 0⟩ : Z)
     else ⟨0, f.rndMag r (z.neg - z.pos)⟩) := rfl
theorem def_Format_round_gradual (f : Format) (r : Rounding) (z : Z) :
    f.round r .gradual z = f.roundG r z := rfl
theorem def_Format_round_flush (f : Format) (r : Rounding) (z : Z) : f.round r .flush z =
    (if Nat.blt (Z.mag z) f.nmin = true then Z.zero else f.roundG r z) := rfl
theorem def_Format_read_gradual (f : Format) (z : Z) : f.read .gradual z = z := rfl
theorem def_Format_read_flush (f : Format) (z : Z) : f.read .flush z =
    (if Nat.blt (Z.mag z) f.nmin = true then Z.zero else z) := rfl
theorem def_Format_readQ_gradual (f : Format) (z : Z) : f.readQ .gradual z = z := rfl
theorem def_Format_readQ_flush (f : Format) (z : Z) : f.readQ .flush z =
    (if Nat.blt (Z.mag z) (2 ^ f.t) = true then Z.zero else z) := rfl
theorem def_OnGrid (K : Nat) (z : Z) :
    OnGrid K z = (∃ cp cn : Nat, z.pos = cp * 2 ^ K ∧ z.neg = cn * 2 ^ K) := rfl
theorem def_Format_IsFloat (f : Format) (z : Z) : f.IsFloat z =
    ((z.pos = 0 ∨ z.neg = 0) ∧
     (∃ m j : Nat, Z.mag z = m * 2 ^ (f.K + j) ∧ m < 2 ^ (f.t + 1)) ∧
     Z.mag z ≤ f.maxF) := rfl

-- The device: format, rounding, underflow, contraction.
theorem def_Device (f : Format) (r : Rounding) (u : Underflow) (ct : Bool) :
    (Device.mk f r u ct).fmt = f ∧ (Device.mk f r u ct).rounding = r ∧
      (Device.mk f r u ct).underflow = u ∧ (Device.mk f r u ct).contract = ct :=
  ⟨rfl, rfl, rfl, rfl⟩
theorem def_Device_W (f : Format) (u : Underflow) (ct : Bool) :
    (Device.mk f .nearestEven u ct).W = 2 ^ (f.t + 1) ∧ (Device.mk f .towardZero u ct).W = 2 ^ f.t :=
  ⟨rfl, rfl⟩
theorem def_Device_etaG (f : Format) (ct : Bool) :
    (Device.mk f .nearestEven .gradual ct).etaG = 2 ^ (f.K - 1) ∧
      (Device.mk f .towardZero .gradual ct).etaG = 2 ^ f.K ∧
      (Device.mk f .nearestEven .flush ct).etaG = f.nmin ∧
      (Device.mk f .towardZero .flush ct).etaG = f.nmin := ⟨rfl, rfl, rfl, rfl⟩
theorem def_Device_etaA (f : Format) (r : Rounding) (ct : Bool) :
    (Device.mk f r .gradual ct).etaA = 0 ∧ (Device.mk f r .flush ct).etaA = f.nmin := ⟨rfl, rfl⟩
theorem def_Device_etaR (f : Format) (r : Rounding) (ct : Bool) :
    (Device.mk f r .gradual ct).etaR = 0 ∧ (Device.mk f r .flush ct).etaR = f.nmin := ⟨rfl, rfl⟩
theorem def_Device_rnd (d : Device) (z : Z) : d.rnd z = d.fmt.round d.rounding d.underflow z := rfl
theorem def_Device_rd (d : Device) (z : Z) : d.rd z = d.fmt.read d.underflow z := rfl
theorem def_Device_rdQ (d : Device) (z : Z) : d.rdQ z = d.fmt.readQ d.underflow z := rfl
theorem def_Device_finite (d : Device) (z : Z) : d.finite z = Nat.ble (Z.mag z) d.fmt.maxF := rfl
-- The model a device instantiates: its own functions and constants, on its own grid.
theorem def_Device_model (d : Device) :
    d.model.W = d.W ∧ d.model.etaG = d.etaG ∧ d.model.etaA = d.etaA ∧ d.model.etaR = d.etaR ∧
      d.model.rnd = d.rnd ∧ d.model.rd = d.rd ∧ d.model.rdQ = d.rdQ ∧
      d.model.finite = d.finite ∧ d.model.contract = d.contract ∧ d.model.D = OnGrid d.fmt.K :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Evaluation of a schedule: any bracketing (the tree), overflow as `none`, contraction.
theorem def_Model_fin (M : Model) (z : Z) :
    M.fin z = (if M.finite z = true then some z else none) := rfl
theorem def_eval_leaf (M : Model) (v : Z) : eval M (.leaf v) = some (M.rd v) := rfl
theorem def_eval_prod (M : Model) (x y : Z) :
    eval M (.prod x y) = M.fin (M.rnd (Z.mul (M.rdQ x) (M.rdQ y))) := rfl
theorem def_eval_add (M : Model) (l r : Sched) : eval M (.add l r) =
    (match eval M l, eval M r with
     | some a, some b => M.fin (M.rnd (Z.add a b))
     | _, _ => none) := rfl
theorem def_eval_fma (M : Model) (x y : Z) (t : Sched) : eval M (.fma x y t) =
    (match eval M t with
     | some c =>
       if M.contract = true then M.fin (M.rnd (Z.add (Z.mul (M.rdQ x) (M.rdQ y)) c))
       else
         (match M.fin (M.rnd (Z.mul (M.rdQ x) (M.rdQ y))) with
          | some p => M.fin (M.rnd (Z.add p c))
          | none => none)
     | none => none) := rfl
theorem def_nmax (a b : Nat) : nmax a b = (if Nat.ble a b = true then b else a) := rfl
theorem def_Sched_height (v x y : Z) (l r t : Sched) :
    (Sched.leaf v).height = 0 ∧ (Sched.prod x y).height = 0 ∧
      (Sched.add l r).height = nmax l.height r.height + 1 ∧
      (Sched.fma x y t).height = t.height + 1 := ⟨rfl, rfl, rfl, rfl⟩
theorem def_Sched_IsSum (v x y : Z) (l r t : Sched) :
    (Sched.leaf v).IsSum = True ∧ (Sched.prod x y).IsSum = False ∧
      (Sched.add l r).IsSum = (l.IsSum ∧ r.IsSum) ∧ (Sched.fma x y t).IsSum = False :=
  ⟨rfl, rfl, rfl, rfl⟩
theorem def_Sched_IsDot (v x y : Z) (l r t : Sched) :
    (Sched.leaf v).IsDot = False ∧ (Sched.prod x y).IsDot = True ∧
      (Sched.add l r).IsDot = (l.IsDot ∧ r.IsDot) ∧ (Sched.fma x y t).IsDot = t.IsDot :=
  ⟨rfl, rfl, rfl, rfl⟩
-- The operands of a schedule; a permutation of them (`List.Perm`) is what the theorems take.
theorem def_Sched_leaves (v x y : Z) (l r t : Sched) :
    (Sched.leaf v).leaves = [v] ∧ (Sched.prod x y).leaves = [] ∧
      (Sched.add l r).leaves = l.leaves ++ r.leaves ∧ (Sched.fma x y t).leaves = [] :=
  ⟨rfl, rfl, rfl, rfl⟩
theorem def_Sched_pairs (v x y : Z) (l r t : Sched) :
    (Sched.leaf v).pairs = [] ∧ (Sched.prod x y).pairs = [(x, y)] ∧
      (Sched.add l r).pairs = l.pairs ++ r.pairs ∧ (Sched.fma x y t).pairs = (x, y) :: t.pairs :=
  ⟨rfl, rfl, rfl, rfl⟩
theorem def_zsum (x : Z) (xs : List Z) :
    zsum [] = Z.zero ∧ zsum (x :: xs) = Z.add x (zsum xs) := ⟨rfl, rfl⟩
theorem def_magSum (x : Z) (xs : List Z) :
    magSum [] = 0 ∧ magSum (x :: xs) = Z.mag x + magSum xs := ⟨rfl, rfl⟩
theorem def_dotZ (p : Z × Z) (ps : List (Z × Z)) :
    dotZ [] = Z.zero ∧ dotZ (p :: ps) = Z.add (Z.mul p.1 p.2) (dotZ ps) := ⟨rfl, rfl⟩
theorem def_dotAbs (p : Z × Z) (ps : List (Z × Z)) :
    dotAbs [] = 0 ∧ dotAbs (p :: ps) = Z.mag (Z.mul p.1 p.2) + dotAbs ps := ⟨rfl, rfl⟩

-- What a witness asserts.
theorem def_Regime (rel abs : Nat) :
    Regime false rel abs = (abs ≤ rel) ∧ Regime true rel abs = (rel < abs) := ⟨rfl, rfl⟩
theorem def_Format_IsFloatQ (f : Format) (z : Z) : f.IsFloatQ z =
    ((z.pos = 0 ∨ z.neg = 0) ∧
     (∃ m j : Nat, Z.mag z = m * 2 ^ j ∧ m < 2 ^ (f.t + 1)) ∧
     Z.mag z * 2 ^ f.K ≤ f.maxF) := rfl
theorem def_Sched_hasFma (v x y : Z) (l r t : Sched) :
    (Sched.leaf v).hasFma = false ∧ (Sched.prod x y).hasFma = false ∧
      (Sched.add l r).hasFma = (match l.hasFma with
        | true => true
        | false => r.hasFma) ∧
      (Sched.fma x y t).hasFma = true := ⟨rfl, rfl, rfl, rfl⟩
theorem def_SumAttained (d : Device) (cn cd : Nat) (uf : Bool) : SumAttained d cn cd uf =
    (∃ xs : List Z, ∃ t : Sched, ∃ c : Z, ∃ hb : Nat,
      t.IsSum ∧ List.Perm t.leaves xs ∧ (∀ x : Z, x ∈ xs → d.fmt.IsFloat x) ∧
      eval d.model t = some c ∧ t.height ≤ hb ∧ hb < d.W ∧
      2 ≤ xs.length ∧ 0 < Z.dist c (zsum xs) ∧ 0 < cd ∧
      Regime uf (hb * magSum xs) (d.W * (xs.length * d.etaR + (xs.length - 1) * d.etaA)) ∧
      cd * (hb * magSum xs + d.W * (xs.length * d.etaR + (xs.length - 1) * d.etaA)) ≤
        cn * ((d.W - hb) * Z.dist c (zsum xs))) := rfl
theorem def_DotAttained (d : Device) (cn cd : Nat) (uf : Bool) : DotAttained d cn cd uf =
    (∃ ps : List (Z × Z), ∃ t : Sched, ∃ c : Z, ∃ hb : Nat,
      t.IsDot ∧ t.hasFma = true ∧ List.Perm t.pairs ps ∧
      (∀ q : Z × Z, q ∈ ps → d.rdQ q.1 = q.1 ∧ d.rdQ q.2 = q.2) ∧
      (∀ q : Z × Z, q ∈ ps → d.fmt.IsFloatQ q.1 ∧ d.fmt.IsFloatQ q.2) ∧
      eval d.model t = some c ∧ t.height ≤ hb ∧ hb + 1 < d.W ∧
      2 ≤ ps.length ∧ 0 < Z.dist c (dotZ ps) ∧ 0 < cd ∧
      Regime uf ((hb + 1) * dotAbs ps)
        (d.W * (ps.length * d.etaG + (ps.length - 1) * d.etaA)) ∧
      cd * ((hb + 1) * dotAbs ps + d.W * (ps.length * d.etaG + (ps.length - 1) * d.etaA)) ≤
        cn * ((d.W - (hb + 1)) * Z.dist c (dotZ ps))) := rfl

-- The prelude's definitions the statements use directly: the length `n` of the operand list
-- (the `n` of `n * etaR + (n - 1) * etaA`) and membership (the scope of the hypotheses on the
-- operands). Membership is the predicate these two facts determine.
theorem def_List_length (α : Type) (x : α) (xs : List α) :
    ([] : List α).length = 0 ∧ (x :: xs).length = xs.length + 1 := ⟨rfl, rfl⟩
theorem def_List_mem (α : Type) (x : α) (xs : List α) : (x ∈ xs) = List.Mem x xs := rfl
theorem def_List_mem_nil (α : Type) (x : α) : ¬ x ∈ ([] : List α) := List.not_mem_nil x
theorem def_List_mem_cons (α : Type) (x y : α) (ys : List α) :
    x ∈ y :: ys ↔ x = y ∨ x ∈ ys := List.mem_cons

end ReductionBoundDefPins
"#;

/// Definition pins, by content. The kernel's closure digest of each definition
/// the headline statements and the witness predicates are written in, the
/// prelude's among them (`List.Perm`, `List.length`, list membership). Not
/// here, on purpose: `Device.model`, `SumAttained` and `DotAttained`
/// (`RESTATED_ONLY`). Their closures contain the proofs of the model's laws, so
/// their digests would move with every proof edit; they are pinned in full by
/// `def_Device_model`, `def_SumAttained` and `def_DotAttained` above, over
/// names pinned here.
const DEFINITION_DIGESTS: [(&str, &str); 57] = [
    (
        "ReductionBound.adiff",
        "d1a3210ed972359c60009a15729b1dad02ffa396e187a3d6511756c66be0f783",
    ),
    (
        "ReductionBound.Z",
        "b06547e1747006ee95c4d45c9ed2c83d2a095204b19825701b828552943b30e5",
    ),
    (
        "ReductionBound.Z.zero",
        "505c89908b7285a9ed82c7a01cb3b948bb71ca28f926fe963be228bfc8fe2de0",
    ),
    (
        "ReductionBound.Z.add",
        "ddcaedcfc53a645a428dea65aeaddd80fdf2bbe99541c96052422a9f7010f2c5",
    ),
    (
        "ReductionBound.Z.mul",
        "d38f1cb72a6ed17d53dad1ea2faeea4b395e5d90eb5e5567ee97ec3260f9cd7e",
    ),
    (
        "ReductionBound.Z.mag",
        "697bd2d6980a5b8eb06d610c2698797b91eb380ce1c33b8d5570dfe4a997d829",
    ),
    (
        "ReductionBound.Z.dist",
        "c344f7ebbd07ed33959c4a7cc8772d426f8a297cf5f480f59b90a5fdd83d5cee",
    ),
    (
        "ReductionBound.Format",
        "26837454547ef2bd6b037c52f35fcdbf4ce501ea90f2d7e5de028c2b21f046e9",
    ),
    (
        "ReductionBound.Format.K",
        "3bda45465b4efe4eeffd1d0f2b46afc7eb49e019f2da42f86dd0bcf1a6229414",
    ),
    (
        "ReductionBound.Format.E",
        "2831200f348c30628f7ca2561492548b20eab57a69752ea95e37ed7743a1f73e",
    ),
    (
        "ReductionBound.Format.nmin",
        "4dc4ad2f2250809d91f2c996c93634401d4a183fbb849a01b41dbfc80ec12d48",
    ),
    (
        "ReductionBound.Format.maxF",
        "cec5b4eb0f833d593037c7b39b84a8f844c164faf65400af38a0a8071a48924b",
    ),
    (
        "ReductionBound.binary32",
        "6f15337f4d27701b11bc6a3f680bffaac3ec9c6b5eb788bcd27d4e6b0523065b",
    ),
    (
        "ReductionBound.binary64",
        "2dbb623d564cb69eb35dbce90efd6ee973cf0eec3413acaec96fd3e87937a0eb",
    ),
    (
        "ReductionBound.Rounding",
        "79c9fe89ac97a2fc4ae4fdd14aca7ec8a9b3a57e7460cf79a8444261c9349def",
    ),
    (
        "ReductionBound.Underflow",
        "4c11ad0912df798aeb3f2950fc0a5d48490dff6f39a25fe3e8add09b96189953",
    ),
    (
        "ReductionBound.expSearch",
        "6666c431ece4e4a71666badd292b6d323ed157d315ff662a211a08b8d3656020",
    ),
    (
        "ReductionBound.Format.expo",
        "5bec48e6b0f412fbdc52ccb2137be79428fd4d62ffcdea7aad713f58692703fa",
    ),
    (
        "ReductionBound.rndAt",
        "9518f348e4c31f3f6489764abab8a63fe454af9fa89bbecb7fe76815b0ad317a",
    ),
    (
        "ReductionBound.Format.rndMag",
        "469d457256da6a3cd32e60fed4b345efd007a0b6fd3fa5d1e1c419e558d89b1a",
    ),
    (
        "ReductionBound.Format.roundG",
        "35d9c459b3190105b8a4a6d6ef5dbebc89596c03e399beed5ef6930938464cc1",
    ),
    (
        "ReductionBound.Format.round",
        "4125ebaa448184600e7e384f199cd3da0b2a49d78080450864fddee40632dcb6",
    ),
    (
        "ReductionBound.Format.read",
        "506d38ca585f26895eef3949bab09faf3123f49f66613b66da0654603416bd54",
    ),
    (
        "ReductionBound.Format.readQ",
        "d9d60ef881fa1a87b70e34f8a6caec6c523c9d3105f5de4eb8b3ff88b203042f",
    ),
    (
        "ReductionBound.OnGrid",
        "35044fcd0ee121fb543411c3ee3c3c7bd5c9e75e1c809293498778d526268bc6",
    ),
    (
        "ReductionBound.Format.IsFloat",
        "d5aeb4ca5b806827ad090c13ca4525a587055f468c6e57e9c1e5ace3fb44e669",
    ),
    (
        "ReductionBound.Device",
        "f980df6044e1881bb67a91418f0a3711c0e2e555041671cc22059b034e309968",
    ),
    (
        "ReductionBound.Device.W",
        "92d0f8b23bc83033dda8d8b2f17a176d3105257a09e1d4a6308af88ddba9daff",
    ),
    (
        "ReductionBound.Device.etaG",
        "9fc05cb6f8ea4fe782fcee00f66dd9db4d609dcb12090566311fc62fef7e82c8",
    ),
    (
        "ReductionBound.Device.etaA",
        "834322931a537f7e58ce1d669de82d67d04676903b2da6d7ff9e98f70d3283e3",
    ),
    (
        "ReductionBound.Device.etaR",
        "39130ee849d5ad6ff188b0d75ee3aeae2fb65feb0ab33e13c51b28a04ebc3f62",
    ),
    (
        "ReductionBound.Device.rnd",
        "71bbe20395ad255331d0cb326aa70d0545e8a72edfa7b73edd8f33583a636cff",
    ),
    (
        "ReductionBound.Device.rd",
        "1b6dd1866abd14ac7f57936125e681664584cfa6220eb2005ab134ef53b9bef2",
    ),
    (
        "ReductionBound.Device.rdQ",
        "3e94ef05fed364c01e5aca793165fd4ac9bdeb9b0cb57567a9abd54f645e869a",
    ),
    (
        "ReductionBound.Device.finite",
        "d2eb287159cba967122531250e57fbea8f34b308ab34cd8df9febd250d6eb0a0",
    ),
    (
        "ReductionBound.Model",
        "7e7e099abf17c3724e221abd912865b8f95c219df81af78e78081a5a0f4fb7aa",
    ),
    (
        "ReductionBound.Model.fin",
        "ef81bc2f6a7e6668115f33affcb210fc28afa88dac0a47cc4163afc01bd05a6d",
    ),
    (
        "ReductionBound.Sched",
        "32cff1585c17349aa769cc20b4e32cf77a9e5dcccf822014c27f237e44735376",
    ),
    (
        "ReductionBound.eval",
        "dcf7a34313bb9764705c057fb8ada5b10037a7fb18b7a0d86acfc7b60f667355",
    ),
    (
        "ReductionBound.nmax",
        "7ad3d716ea25311f40fea8d8ceff94dd2f608162ec3992a6ca16b4ff3c188cea",
    ),
    (
        "ReductionBound.Sched.height",
        "d3112eca1f6ceaa7331ae8ff75e2e3c367ffd4e4a3b50f61f319ab3981839fdf",
    ),
    (
        "ReductionBound.Sched.IsSum",
        "ce1fc31a9d8d5dbfc72b6aa318813f2629382ed47cbff213803f419d4e5ed492",
    ),
    (
        "ReductionBound.Sched.IsDot",
        "d71edfec6c0e5a2c0c64cce2447c2e51a344e2ccf24ad1c2a0fff6a9e98780c5",
    ),
    (
        "ReductionBound.Sched.leaves",
        "b1457aa8db3808e0b76096fc379bf5b7938bdc51117f5b59371ef9d538739440",
    ),
    (
        "ReductionBound.Sched.pairs",
        "252226eb6823502cc89b7351229bfdc9249d9ef22530ef253792cf0563eb21b8",
    ),
    (
        "ReductionBound.zsum",
        "d999072bf38473fe8a2871f94ace06f7dad787c4150630d53d5b481a05535a49",
    ),
    (
        "ReductionBound.magSum",
        "eee325f206db8b1b326ea3d0c5140a92cb601d83cafc9d0be4acca07f9109a36",
    ),
    (
        "ReductionBound.dotZ",
        "1374f2f5cedffcd8f1370d199198e448ceb4cde8bc1fbeeb330b6b2acea4ea5c",
    ),
    (
        "ReductionBound.dotAbs",
        "6cf8eeddf3c42c1268fb819840a1dbd3d8f3219c8b28ec376d59c434371a1e88",
    ),
    (
        "ReductionBound.Regime",
        "66fbf42acc4e2cd8350cb605a5c46a8cd04b66eb2bf454118f9b761e20f00ffa",
    ),
    (
        "ReductionBound.Format.IsFloatQ",
        "2e80536eb9fde5436a7b82d7020637de361eab23ad1d9a8706fbfa66784ea9ad",
    ),
    (
        "ReductionBound.Sched.hasFma",
        "0d31495b5de59fe67455c9698a4f1c2e43af06ac48c89c9c7a51f7a753eb4f49",
    ),
    (
        "List.Perm",
        "d27f1884402961015cc7c275b33292af5ae7352b2637d5105a2991057cec6a06",
    ),
    (
        "List.length",
        "394b7638b97e68f095b4edf3cc967f421cc6ae9a16c2173257a3ba498c39faf1",
    ),
    (
        "Membership.mem",
        "f2c631b9539fd58567290b55976606130f559ef6ba225e7a964e19b916042524",
    ),
    (
        "List.instMembership",
        "c54d671e0dd47bba2676307cbab1b083360444b1323a463a6f09b2295670292f",
    ),
    (
        "List.Mem",
        "15df89b6bb4f90a1e2a5251848ce3e16d276b743c5d69dd2b31f313e8cb2e7a9",
    ),
];

/// The names the statements use that have no digest row, on purpose: each is
/// restated in full by an `rfl` pin (`def_Device_model`, `def_SumAttained`,
/// `def_DotAttained`) over names that have one.
const RESTATED_ONLY: [&str; 3] = [
    "ReductionBound.Device.model",
    "ReductionBound.SumAttained",
    "ReductionBound.DotAttained",
];

/// The witness predicates: what an example of a theorem asserts.
const WITNESS_PREDICATES: [&str; 2] = ["ReductionBound.SumAttained", "ReductionBound.DotAttained"];

/// Which of the three theorems a witness is an example of.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Theorem {
    /// `reduction_bound_sum_*`.
    Sum,
    /// `reduction_bound_dot_*` on a device that does not contract.
    DotNotFused,
    /// `reduction_bound_dot_*` on a device that contracts `x * y + c`.
    DotFused,
}

/// Which term of the bound dominates in a witness.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Regime {
    /// The relative term `h * sum|x_i|` is at least the underflow term.
    Relative,
    /// The underflow term `W * H` exceeds the relative term.
    Underflow,
}

/// The factor `c` of a witness: `error >= bound / c`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Factor {
    /// `c = (2^k + 1) / 2^k = 1 + 2^-k`.
    OnePlusPow2Neg(u32),
    /// `c = 3 (2^k + 1) / 2^(k+1) = 3/2 * (1 + 2^-k)`.
    ThreeHalvesTimes(u32),
}

impl Factor {
    /// `(cn, cd)` as Clean terms, `c = cn / cd`.
    fn terms(self) -> (String, String) {
        match self {
            Factor::OnePlusPow2Neg(k) => (format!("(2 ^ {k} + 1)"), format!("(2 ^ {k})")),
            Factor::ThreeHalvesTimes(k) => {
                (format!("(3 * (2 ^ {k} + 1))"), format!("(2 ^ {})", k + 1))
            }
        }
    }

    /// `(cn, cd)` as numbers.
    fn ratio(self) -> (u128, u128) {
        match self {
            Factor::OnePlusPow2Neg(k) => {
                assert!(k < 100, "exponent {k} out of range");
                ((1u128 << k) + 1, 1u128 << k)
            }
            Factor::ThreeHalvesTimes(k) => {
                assert!(k < 100, "exponent {k} out of range");
                (3 * ((1u128 << k) + 1), 1u128 << (k + 1))
            }
        }
    }

    /// `self <= cn / cd`.
    fn at_most(self, (cn, cd): (u128, u128)) -> bool {
        let (n, d) = self.ratio();
        n * cd <= cn * d
    }

    fn show(self) -> String {
        match self {
            Factor::OnePlusPow2Neg(k) => format!("1 + 2^-{k}"),
            Factor::ThreeHalvesTimes(k) => format!("3/2 * (1 + 2^-{k})"),
        }
    }
}

/// One kernel-checked example: the named theorem of `proofs/reduction_bound.lean`
/// states `SumAttained` / `DotAttained` for this device, factor and regime.
#[derive(Clone, Debug)]
struct Witness {
    name: String,
    theorem: Theorem,
    format: &'static str,
    rounding: &'static str,
    underflow: &'static str,
    regime: Regime,
    factor: Factor,
}

/// The witnesses and their factors. With precision `p` (24, 53) and the
/// rounding's factor `r = 1 + 2^(3-p)` to nearest even, `r = 1 + 2^(4-p)` toward
/// zero:
///
/// - relative regime, every mode: `r`. The schedule has height 2 (sum) or 1
///   with a product (dot), and every rounding it performs loses the most its
///   mode can lose, so the only slack is the theorem's `W - h` against `W`;
/// - underflow regime, gradual underflow (dot products only: a sum of floats
///   does not underflow gradually, `etaA = etaR = 0`): `r`, on two products
///   that each lose all of a half (nearest) or nearly all of a whole (toward
///   zero) quantum;
/// - underflow regime, flushing: `3/2 r`. The theorem charges `n` read errors
///   and `n - 1` addition errors (a sum), or `n` product errors and `n - 1`
///   addition errors (a dot product), of up to `nmin` each. With two operands
///   that is `3 nmin`, and the witnesses lose `2 nmin` of it: operands (or
///   products) that are flushed leave nothing for the addition to flush. So
///   the bound's underflow term is attained within `3/2` here, not within a
///   factor near 1; exactly `3/2` is refused by the kernel. No input with
///   more of the three errors was found, and none is claimed not to exist.
///
/// One witness per theorem, format, rounding and underflow mode in the relative
/// regime (24), and one in the underflow regime wherever the device has an
/// underflow term for that theorem (20: a sum under gradual underflow has none).
fn witnesses() -> Vec<Witness> {
    let mut out = Vec::new();
    for (format, fmt, precision) in [("binary32", "b32", 24u32), ("binary64", "b64", 53u32)] {
        for (rounding, rnd, lost) in [("nearestEven", "rne", 3u32), ("towardZero", "rtz", 4u32)] {
            let rounding_factor = Factor::OnePlusPow2Neg(precision - lost);
            for underflow in ["gradual", "flush"] {
                for theorem in [Theorem::Sum, Theorem::DotNotFused, Theorem::DotFused] {
                    let stem = match theorem {
                        Theorem::Sum => "",
                        Theorem::DotNotFused => "_unfused",
                        Theorem::DotFused => "_fused",
                    };
                    let kind = if theorem == Theorem::Sum {
                        "sum"
                    } else {
                        "dot"
                    };
                    out.push(Witness {
                        name: format!("{kind}_attained{stem}_{fmt}_{rnd}_{underflow}"),
                        theorem,
                        format,
                        rounding,
                        underflow,
                        regime: Regime::Relative,
                        factor: rounding_factor,
                    });
                    if theorem == Theorem::Sum && underflow == "gradual" {
                        continue;
                    }
                    out.push(Witness {
                        name: format!("{kind}_attained_underflow{stem}_{fmt}_{rnd}_{underflow}"),
                        theorem,
                        format,
                        rounding,
                        underflow,
                        regime: Regime::Underflow,
                        factor: if underflow == "flush" {
                            Factor::ThreeHalvesTimes(precision - lost)
                        } else {
                            rounding_factor
                        },
                    });
                }
            }
        }
    }
    out
}

/// No witness may state a factor above `1 + 2^-20`, except where the underflow
/// term of a flushing device dominates: there none may state one above `8/5`
/// (`3/2 * (1 + 2^-k)` is below it).
const MAX_FLUSHED_UNDERFLOW_FACTOR: (u128, u128) = (8, 5);
const MAX_FACTOR: (u128, u128) = ((1 << 20) + 1, 1 << 20);

/// The pin of one witness: its statement written out, proved by its theorem.
fn witness_pin(wit: &Witness) -> String {
    let (cn, cd) = wit.factor.terms();
    let predicate = match wit.theorem {
        Theorem::Sum => "SumAttained",
        Theorem::DotNotFused | Theorem::DotFused => "DotAttained",
    };
    let contract = wit.theorem == Theorem::DotFused;
    let underflow_dominates = wit.regime == Regime::Underflow;
    format!(
        "theorem pin_{name} : ReductionBound.{predicate} \
         (ReductionBound.Device.mk ReductionBound.{format} ReductionBound.Rounding.{rounding} \
         ReductionBound.Underflow.{underflow} {contract}) {cn} {cd} {underflow_dominates} := \
         ReductionBound.{name}\n",
        name = wit.name,
        format = wit.format,
        rounding = wit.rounding,
        underflow = wit.underflow,
    )
}

fn hex(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for b in bytes {
        let _ = write!(out, "{b:02x}");
    }
    out
}

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

/// The constants an expression of `name` mentions: its type, and its value too
/// when `with_value` (a predicate's meaning is its body; a theorem's is its
/// statement).
fn mentioned(env: &Environment, name: &str, with_value: bool) -> HashSet<Name> {
    let Some(info) = env.get_const(&Name::from_string(name)) else {
        panic!("{name} must be registered");
    };
    let mut refs = HashSet::new();
    info.type_
        .used_constants_dag(UsedConstants::WithProjectionStructures, &mut refs);
    if with_value {
        let Some(value) = &info.value else {
            panic!("{name} must be a definition");
        };
        value.used_constants_dag(UsedConstants::WithProjectionStructures, &mut refs);
    }
    refs
}

/// Every constant a headline statement or a witness predicate mentions that no
/// pin covers: it is in no digested name's closure and is not restated in full
/// (`RESTATED_ONLY`). `digested` is the names that have a digest row. Each
/// entry reads `constant (mentioned by ...)`.
fn unpinned_statement_constants(env: &Environment, digested: &[&str]) -> Vec<String> {
    let mut pinned: HashSet<Name> = RESTATED_ONLY.iter().map(|n| Name::from_string(n)).collect();
    for name in digested {
        match env.dependency_closure(&Name::from_string(name)) {
            Ok(members) => pinned.extend(members),
            Err(e) => panic!("{name}: no dependency closure: {e:?}"),
        }
    }
    let mut out = BTreeSet::new();
    let statements = HEADLINES
        .iter()
        .map(|h| (*h, false))
        .chain(WITNESS_PREDICATES.iter().map(|p| (*p, true)));
    for (name, with_value) in statements {
        for constant in mentioned(env, name, with_value) {
            if !pinned.contains(&constant) {
                out.insert(format!("{constant} (mentioned by {name})"));
            }
        }
    }
    out.into_iter().collect()
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

    // The definitions the statements are written in: restated, then by content.
    if let Err(e) = elaborate_into(&mut env, DEFINITION_PINS) {
        panic!("a definition no longer unfolds to its pin:\n{e}");
    }
    // The pins are complete for the statements: nothing a headline statement
    // or a witness predicate mentions is outside them.
    let digested: Vec<&str> = DEFINITION_DIGESTS.iter().map(|(name, _)| *name).collect();
    let unpinned = unpinned_statement_constants(&env, &digested);
    assert!(
        unpinned.is_empty(),
        "the statements mention {} constant(s) no definition pin covers; give each a row in \
         DEFINITION_DIGESTS and a restating equation in DEFINITION_PINS:\n{}",
        unpinned.len(),
        unpinned.join("\n")
    );
    // That check is live: without its row, the length of the operand list is
    // reported for every headline statement that mentions it.
    let without_length: Vec<&str> = digested
        .iter()
        .copied()
        .filter(|name| *name != "List.length")
        .collect();
    let reported = unpinned_statement_constants(&env, &without_length);
    for headline in HEADLINES {
        let entry = format!("List.length (mentioned by {headline})");
        assert!(
            reported.contains(&entry),
            "the completeness check must report `{entry}` when List.length has no row; it reported {reported:?}"
        );
    }

    let mut table = String::new();
    let mut moved = Vec::new();
    for (name, pinned) in &DEFINITION_DIGESTS {
        let digest = match env.closure_digest(&Name::from_string(name)) {
            Ok(d) => hex(&d),
            Err(e) => panic!("{name}: no closure digest: {e:?}"),
        };
        if digest != *pinned {
            moved.push(*name);
        }
        let _ = writeln!(table, "    (\"{name}\", \"{digest}\"),");
    }
    assert!(
        moved.is_empty(),
        "the kernel records of {} pinned definition(s) changed: {moved:?}\n\
         Read the module docs (\"When a definition digest moves\") before pasting:\n\
         const DEFINITION_DIGESTS: [(&str, &str); {}] = [\n{table}];",
        moved.len(),
        DEFINITION_DIGESTS.len()
    );

    // The witnesses: one per theorem, format, rounding and underflow mode.
    let witnesses = witnesses();
    let relative = witnesses
        .iter()
        .filter(|wit| wit.regime == Regime::Relative)
        .count();
    assert_eq!(
        (relative, witnesses.len()),
        (24, 44),
        "3 theorems x 2 formats x 2 roundings x 2 underflow modes, and 20 underflow-regime witnesses"
    );
    let mut pins = String::from("namespace ReductionBoundWitnessPins\n");
    for wit in &witnesses {
        let cap = if wit.regime == Regime::Underflow && wit.underflow == "flush" {
            MAX_FLUSHED_UNDERFLOW_FACTOR
        } else {
            MAX_FACTOR
        };
        assert!(
            wit.factor.at_most(cap),
            "{}: factor {} is above {cap:?}",
            wit.name,
            wit.factor.show()
        );
        pins.push_str(&witness_pin(wit));
    }
    pins.push_str("end ReductionBoundWitnessPins\n");
    if let Err(e) = elaborate_into(&mut env, &pins) {
        panic!("a witness no longer states its mode and factor:\n{e}");
    }
    for wit in &witnesses {
        eprintln!(
            "reduction_bound witness: {:?} {} {} {} {:?}: error >= bound / ({})  [{}]",
            wit.theorem,
            wit.format,
            wit.rounding,
            wit.underflow,
            wit.regime,
            wit.factor.show(),
            wit.name
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

    let in_file = file_theorems(&env, "ReductionBound.").len();
    assert!(
        in_file >= 300,
        "expected the whole development, found only {in_file} theorems"
    );
    // The file's theorems and every pin (`ReductionBoundPins`, `...DefPins`,
    // `...WitnessPins`).
    let theorems = file_theorems(&env, "ReductionBound");
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

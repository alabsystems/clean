// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lean`'s exit status on the files of the pre-landing review of
//! integ/r6 (findings X1-X11), under both modelled releases.
//!
//! The front door's exit 0 says "Lean would accept this file" (R77). Every
//! file below was run on 2026-10-23 through `bin/lean` of pinned Lean 4.8.0
//! and 4.30.0-rc2: `LEAN_REFUSES` files exit 1 under both (the first error
//! line is quoted beside each), `LEAN_ACCEPTS` files exit 0 under both. At
//! 24f74254b `clean lean` exited 0 on every file of both lists (its release
//! binary, built at dd098b6e7). `KNOWN_GAPS` are files Lean accepts that the
//! fixes refuse, in the safe direction; they are pinned at exit 1 so they
//! fail the day the gap closes. The elaborator-level verdicts are pinned in
//! `crates/clean-elab/src/tests_review_r6.rs`.

#![cfg(unix)]

#[path = "support/lean_front_door.rs"]
mod front_door;

use front_door::{lean, scratch, stdout, write, V4_30_0_RC2, V4_8_0};

/// Run every `(file, source)` under both releases and require `expected`.
fn assert_exit(test: &str, cases: &[(&str, &str)], expected: i32) {
    let dir = scratch(test);
    for (file, source) in cases {
        write(&dir, file, source);
        for release in [V4_8_0, V4_30_0_RC2] {
            let run = lean(&dir, release, &[file]);
            assert_eq!(
                run.status.code(),
                Some(expected),
                "{file} under {release}: `clean lean` must exit {expected}; stdout:\n{}",
                stdout(&run)
            );
        }
    }
}

/// Both pinned Leans exit 1 on each (first error line of 4.8.0 quoted).
const LEAN_REFUSES: &[(&str, &str)] = &[
    // X9 "failed to synthesize Inhabited False"
    ("x9_false.lean", "opaque o : False\ntheorem oops : False := o\n"),
    // X9 "failed to synthesize Inhabited Empty"
    ("x9_empty.lean", "opaque o : Empty\ntheorem oops : False := nomatch o\n"),
    // X9 "failed to synthesize Inhabited (Fin n)"
    ("x9_fin.lean", "opaque o (n : Nat) : Fin n\n"),
    // X9 "failed to compile definition, consider marking it as
    // 'noncomputable' because it depends on 'Classical.ofNonempty'"
    (
        "x9_nonempty.lean",
        "structure S where\n  x : Nat\ninstance : Nonempty S := ⟨⟨0⟩⟩\nopaque s : S\n",
    ),
    // X10 "(kernel) invalid declaration, it uses unsafe declaration 'u'"
    ("x10_thm.lean", "unsafe def u : Nat := 1\ntheorem t : u = 1 := rfl\n"),
    ("x10_def.lean", "unsafe def u : Nat := 1\ndef s : Nat := u\n"),
    // X10 "(kernel) invalid declaration, it uses unsafe declaration 'ax'"
    ("x10_axiom.lean", "unsafe axiom ax : False\ntheorem f : False := ax\n"),
    // X10 "'unsafe' theorems are not allowed"
    ("x10_unsafe_thm.lean", "unsafe theorem t : True := True.intro\n"),
    // X11 "cannot evaluate code because 'x' uses 'sorry'"
    ("x11_sorry_def.lean", "def x : Nat := sorry\n#eval x\n"),
    ("x11_sorry_term.lean", "#eval (sorry : Nat)\n"),
    ("x11_sorry_add.lean", "#eval (sorry : Nat) + 1\n"),
    // X11 "failed to compile definition ... depends on 'x'"
    ("x11_noncomp.lean", "noncomputable def x : Nat := 1\n#eval x\n"),
    // Runtime axioms have no executable implementation (compiler eligibility).
    ("fr_p_eval_ax.lean", "axiom a : Nat\n#eval a\n"),
    // X11 "could not synthesize a 'Lean.Eval' instance"
    ("x11_fun.lean", "#eval fun (x : Nat) => x\n"),
    // X1 "... because it depends on 'Classical.ofNonempty'"
    ("x1_ofne.lean", "def x : Nat := Classical.ofNonempty\n"),
    // X1 "... because it depends on 'Classical.choice'"
    ("x1_choice.lean", "def y : Nat := Classical.choice ⟨0⟩\n"),
    (
        "x1_derive.lean",
        "inductive T | a : Nat → T deriving Nonempty\ndef z : T := Classical.ofNonempty\n",
    ),
    ("x1_eval_ofne.lean", "#eval (Classical.ofNonempty : Nat)\n"),
    ("x1_eval_choice.lean", "#eval (Classical.choice ⟨(0:Nat)⟩ : Nat)\n"),
    // X2 "type mismatch"
    (
        "x2_default.lean",
        "def T := Nat\ninstance : Inhabited T := ⟨(5 : Nat)⟩\ntheorem bad : (default : T) = (0 : Nat) := rfl\n",
    ),
    (
        "x2_def.lean",
        "def T := Nat\ninstance : Inhabited T := ⟨(5 : Nat)⟩\ndef z : T := Inhabited.default\ntheorem zv : z = (0 : Nat) := rfl\n",
    ),
    // X2 "failed to synthesize instance Inhabited T"
    ("x2_noinst.lean", "def T := Nat\ndef x : T := default\n"),
    // X6 "type mismatch"
    (
        "x6_uint8.lean",
        "inductive W | p (x : UInt8) | q deriving Inhabited\ntheorem w : (default : W) = W.q := rfl\n",
    ),
    (
        "x6_true.lean",
        "inductive W | p (x : True) | q deriving Inhabited\ntheorem w : (default : W) = W.q := rfl\n",
    ),
    (
        "x6_param.lean",
        "inductive P (α : Type) | a (x : UInt8) | b (y : α) deriving Inhabited\ntheorem w : (default : P Nat) = P.b 0 := rfl\n",
    ),
    // X7 "type mismatch"
    (
        "x7_ill.lean",
        "@[match_pattern] def pr (a : Nat) : Option Nat := some a\ndef h (o : Option Bool) : Bool := match o with\n  | pr b => b\n  | _ => false\n",
    ),
    (
        "x7_int.lean",
        "@[match_pattern] def sNat (n : Nat) : Nat := n + 1\ndef g (i : Int) : Int := match i with\n  | sNat k => k\n  | _ => 0\ntheorem g5 : g 5 = 0 := rfl\n",
    ),
    // X7 "`k` is an explicit pattern variable, but it only occurs in
    // positions that are inaccessible to pattern matching"
    (
        "x7_plain.lean",
        "def g2 (i : Int) : Int := match i with\n  | k + 1 => k\n  | _ => 0\n",
    ),
    // X3 "dependent elimination failed, failed to solve equation"
    (
        "x3_h4.lean",
        "theorem h4 (f : Nat → Nat) (a : Nat) (H : ∀ x, f x = f a) : True := by\n  have b : Nat := a\n  have h := H b\n  cases h\n  trivial\n",
    ),
    (
        "x3_h5.lean",
        "def g : Nat → Nat\n  | 0 => 1\n  | n+1 => n\n\ntheorem h5 (H : ∀ x, g x = 0) : False := by\n  have b : Nat := 0\n  have h := H b\n  cases h\n",
    ),
    // X4 "unknown identifier 'helper'"
    (
        "x4_t1.lean",
        "theorem w4 (n : Nat) (h : n = 0) : (fun _ : Nat => True) 0 := by subst h; exact helper\nwhere helper : (fun _ : Nat => True) n := True.intro\n",
    ),
    (
        "x4_t2.lean",
        "theorem w5 (n m : Nat) (h : n = m) : (fun _ : Nat => True) n := by cases h; exact helper\nwhere helper : (fun _ : Nat => True) m := True.intro\n",
    ),
    (
        "x4_t4.lean",
        "theorem w7 (n : Nat) : True := by\n  cases n\n  · exact helper\n  · exact helper\nwhere\n  helper : (fun _ : Nat => True) n := True.intro\n",
    ),
    // X4 "tactic 'clear' failed, variable 'helper' depends on 'h'"
    (
        "x4_t5.lean",
        "theorem w8 (n : Nat) (h : n = 0) : True := by\n  clear h\n  exact helper\nwhere\n  helper : (fun _ : n = 0 => True) h := True.intro\n",
    ),
    // X5 "failed to create binder due to failure when reverting variable
    // dependencies"
    (
        "x5_o1.lean",
        "theorem o1 (x : Nat) (y : Fin (x+1)) (f : Fin (x+1) → Nat) (h : x = f y) : True := by\n  subst h\n  exact True.intro\n",
    ),
    // X5 "dependent elimination failed, failed to solve equation"
    (
        "x5_o2.lean",
        "theorem o2 (x : Nat) (y : Fin (x+1)) (f : Fin (x+1) → Nat) (h : f y = x) : True := by\n  cases h\n  exact True.intro\n",
    ),
    // X5 "tactic 'subst' failed, 'x' occurs at"
    (
        "x5_o3.lean",
        "theorem o3 (x : Nat) (y : Fin (x+1)) (h : x = y.val) : True := by\n  subst h\n  exact True.intro\n",
    ),
    (
        "x5_o4.lean",
        "theorem o4 (x : Nat) (y : Fin (x+1)) (h : y.val = x) : True := by\n  cases h\n  exact True.intro\n",
    ),
    // X5 "tactic 'subst' failed, did not find equation for eliminating 'n'"
    (
        "x5_v6.lean",
        "theorem v6 (n : Nat) (y : Fin (n+1)) (h : n = y.val) : True := by\n  subst n\n  exact True.intro\n",
    ),
    (
        "x5_p2.lean",
        "theorem p2 (n : Nat) (y : Fin (n+1)) (f : Fin (n+1) → Nat) (h1 : n = f y) (h2 : n = 3) : True := by\n  subst n\n  exact True.intro\n",
    ),
    (
        "x5_p6.lean",
        "theorem p6 (x : Nat) (y : Fin (x+1)) (f : Fin (x+1) → Nat) (h : f y = x) : True := by\n  subst h\n  exact True.intro\n",
    ),
];

/// Both pinned Leans exit 0 on each.
const LEAN_ACCEPTS: &[(&str, &str)] = &[
    ("x9_nat.lean", "opaque o : Nat\ntheorem ok : True := True.intro\n"),
    ("x9_fun.lean", "opaque g : Nat → Nat\n"),
    ("x9_dep.lean", "opaque f (α : Type) [Inhabited α] : α\n"),
    (
        "x9_nonempty_nc.lean",
        "structure S where\n  x : Nat\ninstance : Nonempty S := ⟨⟨0⟩⟩\nnoncomputable opaque s : S\n",
    ),
    ("x10_unsafe.lean", "unsafe def u : Nat := 1\nunsafe def s : Nat := u\n"),
    (
        "x10_partial.lean",
        "partial def p (n : Nat) : Nat := p n\ndef q : Nat := p 0\ntheorem r : q = q := rfl\n",
    ),
    ("x11_add.lean", "#eval (1 : Nat) + 1\n"),
    ("x1_nc.lean", "noncomputable def x : Nat := Classical.ofNonempty\n"),
    ("x1_derive.lean", "inductive T | a : Nat → T deriving Nonempty\n"),
    (
        "x1_prop.lean",
        "def p : Prop := ∃ n : Nat, n = Classical.choice ⟨0⟩\ntheorem t : (Classical.choice ⟨(0:Nat)⟩ : Nat) = Classical.choice ⟨0⟩ := rfl\n",
    ),
    (
        "x2_good.lean",
        "def T := Nat\ninstance : Inhabited T := ⟨(5 : Nat)⟩\ntheorem good : (default : T) = (5 : Nat) := rfl\n",
    ),
    (
        "x2_class.lean",
        "def T := Nat\nclass C (α : Type) where\n  c : α\ninstance : C T := ⟨(5 : Nat)⟩\ndef y : T := C.c\ntheorem yv : y = (5 : Nat) := rfl\n",
    ),
    (
        "x6_rec.lean",
        "inductive T2 | node (l r : T2) | leaf deriving Inhabited\ntheorem w : (default : T2) = T2.leaf := rfl\n",
    ),
    (
        "x6_string.lean",
        "inductive W | p (s : String) | q deriving Inhabited\ntheorem w : (default : W) = W.p \"\" := rfl\n",
    ),
    (
        "x6_param.lean",
        "inductive P (α : Type) | a (y : α) | b deriving Inhabited\ntheorem w : (default : P Nat) = P.b := rfl\n",
    ),
    ("x6_nonempty.lean", "inductive W | p (x : UInt8) | q deriving Nonempty\n"),
    (
        "x7_ok.lean",
        "@[match_pattern] def pr (a : Nat) : Option Nat := some a\ndef h (o : Option Nat) : Nat := match o with\n  | pr b => b\n  | _ => 0\ntheorem h1 : h (some 3) = 3 := rfl\n",
    ),
    (
        "x7_nat.lean",
        "@[match_pattern] def sNat (n : Nat) : Nat := n + 1\ndef g (i : Nat) : Nat := match i with\n  | sNat k => k\n  | _ => 0\ntheorem g5 : g 5 = 4 := rfl\n",
    ),
    (
        "x3_p1.lean",
        "theorem p1 (f : Nat → Nat) (a : Nat) (H : ∀ x, f x = f a) : True := by\n  have h := H a\n  cases h\n  trivial\n",
    ),
    // X3 (R136): a `let` local's value is unfolded by `cases`, a `have`'s is
    // not (`x3_h4`, `x3_h5` above).
    (
        "x3_l4.lean",
        "theorem l4 (f : Nat → Nat) (a : Nat) (H : ∀ x, f x = f a) : True := by\n  let b : Nat := a\n  have h := H b\n  cases h\n  trivial\n",
    ),
    (
        "x3_l5.lean",
        "def g : Nat → Nat\n  | 0 => 1\n  | n+1 => n\n\ntheorem l5 (H : ∀ x, g x = 0) : False := by\n  let b : Nat := 0\n  have h := H b\n  cases h\n",
    ),
    (
        "x4_t3.lean",
        "theorem w3 (n : Nat) (h : n = 0) : (fun _ : Nat => True) 0 := by subst h; exact helper\nwhere helper : (fun _ : Nat => True) 1 := True.intro\n",
    ),
    (
        "x4_t6.lean",
        "theorem w9 (n : Nat) (h : n = 0) : (fun _ : Nat => True) 0 := by\n  subst h\n  exact helper\nwhere\n  helper : True := True.intro\n",
    ),
    (
        "x4_w3.lean",
        "theorem w3 (n m : Nat) (h : n = m) (p : n = 0) : m = 0 := by\n  cases h\n  exact helper\nwhere\n  helper : n = 0 := p\n",
    ),
    (
        "x5_p3.lean",
        "theorem p3 (n : Nat) (y : Fin (n+1)) (h1 : n = y.val) (h2 : n = 3) : True := by\n  subst n\n  exact True.intro\n",
    ),
    (
        "x5_p5.lean",
        "theorem p5 (x z : Nat) (y : Fin (x+1)) (h : x = z) : True := by\n  subst h\n  exact True.intro\n",
    ),
    (
        "x5_v5.lean",
        "theorem v5 (x y : Nat) (h : x = y) : True := by\n  subst h\n  exact True.intro\n",
    ),
];

/// The fix round (2026-10-24): files both pinned Leans exit 0 on that the
/// first fixes refused (`noncomputable section`, `@[implemented_by]` /
/// `@[extern]`, erased types, proofs and parameters, `opaque` of types Lean's
/// `Init` inhabits, section and explicit instances, `unsafe opaque`, `deriving
/// Inhabited` past fields Lean cannot fill either, `ExceptT`'s `default`).
const FIX_ROUND_ACCEPTS: &[(&str, &str)] = &[
    ("fr_nc_sec.lean", "noncomputable section\ndef pick : Nat := Classical.choice ⟨0⟩\nend\n"),
    ("fr_nc_sec_inst.lean", "noncomputable section\ninstance myInst : Inhabited Nat := ⟨Classical.choice ⟨0⟩⟩\nend\n"),
    ("fr_nc_sec_derived.lean", "noncomputable def base : Nat := Classical.choice ⟨0⟩\nnoncomputable section\ndef derived : Nat := base + 1\nend\n"),
    ("fr_nc_sec_comp_eval.lean", "noncomputable section\ndef three : Nat := 3\nend\n#eval three\n"),
    ("fr_ib_def.lean", "def pickImpl (xs : List Nat) : Nat := xs.headD 0\n@[implemented_by pickImpl] def pick (xs : List Nat) : Nat := Classical.choice ⟨xs.length⟩\n"),
    ("fr_ext_def.lean", "@[extern \"lean_my_hash\"] def myHash (n : Nat) : Nat := Classical.choice ⟨n⟩\n"),
    ("fr_er_ctor.lean", "noncomputable def N : Nat := Classical.choice ⟨5⟩\ndef zero : Fin (N+1) := ⟨0, Nat.zero_lt_succ N⟩\n"),
    ("fr_er_proj.lean", "noncomputable def N : Nat := Classical.choice ⟨5⟩\ndef toNat2 (x : Fin (N+1)) : Nat := Fin.val x\n"),
    ("fr_er_have.lean", "noncomputable def N : Nat := Classical.choice ⟨5⟩\ndef k (n : Nat) : Nat := have h : N = N := rfl; n + 1\n"),
    ("fr_er_fvar.lean", "noncomputable def N : Nat := Classical.choice ⟨5⟩\ndef use (g : (n : Nat) → N = N → Nat) : Nat := g 0 rfl\n"),
    ("fr_er_beta.lean", "def x : Nat := (fun (_ : True) => 0) (id (Classical.choice ⟨True.intro⟩))\n"),
    ("fr_op_int.lean", "opaque o : Int\n"),
    ("fr_op_u64.lean", "opaque hash : String → UInt64\n"),
    ("fr_op_prod.lean", "opaque o : Nat × Nat\n"),
    ("fr_op_true.lean", "opaque o : True\n"),
    ("fr_op_sort.lean", "universe u\nopaque o : Sort u\n"),
    ("fr_op_finsucc.lean", "opaque f (n : Nat) : Fin (n+1)\n"),
    ("fr_op_secvar.lean", "variable {α : Type} [Inhabited α]\nopaque o : α\n"),
    ("fr_op_explicit_inst.lean", "opaque o (α : Type) (inst : Inhabited α) : α\n"),
    ("fr_op_prop_nonempty.lean", "opaque o (p : Prop) [Nonempty p] : p\n"),
    ("fr_op_unsafe.lean", "unsafe opaque o : False\n"),
    ("fr_op_ext_nonempty.lean", "structure Ptr where\n  addr : Nat\ninstance : Nonempty Ptr := ⟨⟨0⟩⟩\n@[extern \"alloc_ptr\"] opaque alloc : Nat → Ptr\n"),
    ("fr_dv_ast.lean", "inductive BinOp\n  | add | sub | mul\ninductive MyExpr\n  | bin (op : BinOp) (l r : MyExpr)\n  | lit (n : Nat)\n  | var (name : String)\n  deriving Inhabited\ntheorem t : (default : MyExpr) = MyExpr.lit 0 := rfl\n"),
    ("fr_dv_prop.lean", "inductive B\n  | byte (n : Nat) (h : n < 256)\n  | eof\n  deriving Inhabited\ntheorem t : (default : B) = B.eof := rfl\n"),
    ("fr_dv_pi.lean", "inductive W\n  | sup (f : Nat → W)\n  | leaf\n  deriving Inhabited\ntheorem t : (default : W) = W.leaf := rfl\n"),
    ("fr_dv_param_prod.lean", "inductive Entry (α : Type)\n  | kv (p : α × Nat)\n  | empty\n  deriving Inhabited\ntheorem t : (default : Entry Nat) = Entry.empty := rfl\n"),
    ("fr_x2_exc_err.lean", "theorem good : (default : ExceptT String Id Nat) = (Except.error \"\" : Except String Nat) := rfl\n"),
];

/// The fix round's refusals beside them: both pinned Leans exit 1 on each
/// (a computable use of a constant a `noncomputable section` marked, `#eval`
/// of it, a relevant use of a noncomputable constant, an `opaque` whose type's
/// own binders would supply the instance, `Fin n`, `ExceptT`'s wrong value).
const FIX_ROUND_REFUSES: &[(&str, &str)] = &[
    // `#eval` of an unsynthesized `Decidable`: refused since the fix round
    // (an internal "Unknown free variable" where Lean reports the failed
    // synthesis); it printed a leaked metavariable at 569ec6641.
    ("fr_p_eval_dec.lean", "#eval decide (∀ n : Nat, n = n)\n"),
    ("fr_nc_sec_use_after.lean", "noncomputable section\ndef pick : Nat := Classical.choice ⟨0⟩\nend\ndef use : Nat := pick + 1\n"),
    ("fr_nc_sec_eval.lean", "noncomputable section\ndef pick : Nat := Classical.choice ⟨0⟩\nend\n#eval pick\n"),
    ("fr_er_bad.lean", "noncomputable def N : Nat := Classical.choice ⟨5⟩\ndef bad : Nat := N + 1\n"),
    ("fr_op_pi_inst.lean", "opaque o : ∀ (α : Type) [Inhabited α], α\n"),
    ("fr_op_pi_empty.lean", "opaque o : Nat → [Inhabited Empty] → Empty\n"),
    ("fr_op_pi_nonempty.lean", "noncomputable opaque o : ∀ (α : Type) [Nonempty α], α\n"),
    ("fr_op_fin_n.lean", "opaque o (n : Nat) : Fin n\n"),
    ("fr_x2_exc_ok.lean", "theorem bad : (default : ExceptT String Id Nat) = (Except.ok 0 : Except String Nat) := rfl\n"),
];

/// Both pinned Leans exit 0; Clean refuses each, in the safe direction
/// (`where`-helper hiding after a definitional `simp only … at h`, ledger;
/// `#eval` of a proposition).
const KNOWN_GAPS: &[(&str, &str)] = &[
    ("fr_p_x4_simp.lean", "theorem r3 (n : Nat) (h : n + 0 = 3) : (fun _ : n + 0 = 3 => True) h := by\n  simp only [Nat.add_zero] at h\n  exact helper\nwhere helper : (fun _ : n + 0 = 3 => True) h := True.intro\n"),
    ("fr_p_eval_prop.lean", "#eval (True : Prop)\n"),
];

/// KNOWN FALSE ACCEPTANCES, OPEN: both pinned Leans exit 1 on each (but
/// `fr_x2_opt_none`, which 4.30.0-rc2 accepts and 4.8.0 refuses), and the
/// front door exits 0: the safe context is not checked on an `example`, a
/// `partial def` body, `termination_by` or a `change` hint (R135); `#eval` of
/// a proof, a value with no `Repr`, a function type behind a
/// definition (R134); numeral patterns at a
/// non-reducible alias of `Nat` (R138); `OptionT`'s release-dependent
/// `default` (R70's note). Pinned so each fails the day it closes.
const KNOWN_FALSE_ACCEPTANCES: &[(&str, &str)] = &[
    ("fr_p_ex.lean", "unsafe def u : Nat := 1\nexample : u = 1 := rfl\n"),
    ("fr_p_partial.lean", "unsafe def u : Nat := 1\npartial def p (n : Nat) : Nat := u + p n\n"),
    ("fr_p_change.lean", "unsafe def u : Nat := 1\ntheorem t : 1 = 1 := by\n  change u = 1\n  rfl\n"),
    ("fr_p_term.lean", "unsafe def u : Nat := 1\ndef f : Nat → Nat\n  | 0 => 0\n  | n+1 => f n\ntermination_by n => n + u\n"),
    ("fr_p_eval_proof.lean", "#eval (rfl : 1 = 1)\n"),
    ("fr_p_eval_norepr.lean", "#eval (inferInstance : Inhabited Nat)\n"),
    ("fr_p_eval_fn.lean", "def F := Nat → Nat\ndef g : F := fun x => x\n#eval g\n"),
    ("fr_p_x7_alias.lean", "def T := Nat\ndef pred2 : T → Nat\n  | 0 => 0\n  | n+1 => n\n"),
    ("fr_x2_opt_none.lean", "theorem t : (default : OptionT Id Nat) = (none : Option Nat) := rfl\n"),
];

#[test]
fn test_review_r6_files_lean_refuses_exit_one() {
    assert_exit("review-r6-refuses", LEAN_REFUSES, 1);
}

#[test]
fn test_review_r6_files_lean_accepts_exit_zero() {
    assert_exit("review-r6-accepts", LEAN_ACCEPTS, 0);
}

#[test]
fn test_review_r6_known_gaps_exit_one() {
    assert_exit("review-r6-gaps", KNOWN_GAPS, 1);
}

#[test]
fn test_review_r6_fix_round_lean_accepts_exit_zero() {
    assert_exit("review-r6-fix-accepts", FIX_ROUND_ACCEPTS, 0);
}

#[test]
fn test_review_r6_fix_round_lean_refuses_exit_one() {
    assert_exit("review-r6-fix-refuses", FIX_ROUND_REFUSES, 1);
}

#[test]
fn test_review_r6_known_false_acceptances_exit_zero() {
    assert_exit("review-r6-false-accepts", KNOWN_FALSE_ACCEPTANCES, 0);
}

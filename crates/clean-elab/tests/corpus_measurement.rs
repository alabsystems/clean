// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dedicated elaboration measurement lane for a representative Lean 4 corpus.

#[path = "integration/phase1_corpus_common.rs"]
mod phase1_corpus_common;

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;
use std::any::Any;
use std::collections::BTreeMap;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[derive(Clone, Copy)]
struct CorpusFile {
    name: &'static str,
    category: &'static str,
    source: &'static str,
}

#[derive(Debug)]
struct CorpusError {
    file: &'static str,
    category: &'static str,
    kind: &'static str,
    message: String,
}

struct CorpusMeasurement {
    total: usize,
    passed: usize,
    failed: usize,
    errors: Vec<CorpusError>,
}

macro_rules! corpus_file {
    ($name:literal, $category:literal, $source:expr) => {
        CorpusFile {
            name: $name,
            category: $category,
            source: $source,
        }
    };
}

const CORPUS_FILES: &[CorpusFile] = &[
    corpus_file!(
        "basic_defs_01",
        "basic-defs",
        r#"def basic_nat_zero : Nat := 0
def basic_nat_one : Nat := 1
def basic_nat_add (a b : Nat) : Nat := a + b
def basic_nat_keep_left (a b : Nat) : Nat := a
def basic_nat_twice (n : Nat) : Nat := n + n
"#
    ),
    corpus_file!(
        "basic_defs_02",
        "basic-defs",
        r#"def lambda_id_nat (n : Nat) : Nat := (fun x : Nat => x) n
def let_chain_nat (n : Nat) : Nat := let m := n + 1; m + 2
def let_const_nat : Nat := let x := 3; x
def type_alias_value : Type := Nat
def prop_alias_value : Prop := True
"#
    ),
    corpus_file!(
        "basic_defs_03",
        "basic-defs",
        r#"variable (A : Type)
def var_keep (x : A) : A := x
def var_left (x y : A) : A := x
def var_right (x y : A) : A := y
def var_type : Type := A
"#
    ),
    corpus_file!(
        "basic_defs_04",
        "basic-defs",
        r#"def bool_true_value : Bool := true
def bool_false_value : Bool := false
def bool_flip (b : Bool) : Bool := match b with | true => false | false => true
def unit_value : Unit := Unit.unit
def bool_to_nat_match (b : Bool) : Nat := match b with | true => 1 | false => 0
"#
    ),
    corpus_file!(
        "basic_defs_05",
        "basic-defs",
        r#"def prod_pair : Prod Nat Nat := Prod.mk 1 2
def prod_first (p : Prod Nat Nat) : Nat := p.1
def prod_second (p : Prod Nat Nat) : Nat := p.2
def prod_swap (p : Prod Nat Nat) : Prod Nat Nat := Prod.mk p.2 p.1
theorem prod_first_self : prod_first prod_pair = 1 := rfl
"#
    ),
    corpus_file!(
        "basic_defs_06",
        "basic-defs",
        r#"def succ_zero : Nat := Nat.succ 0
def succ_twice : Nat := Nat.succ (Nat.succ 0)
def use_id_type : Type -> Type := fun A => A
def nat_arrow_id : Nat -> Nat := fun n => n
def const_true : Nat -> Prop := fun _ => True
"#
    ),
    corpus_file!(
        "basic_defs_07",
        "basic-defs",
        r#"def app_fun (f : Nat -> Nat) (n : Nat) : Nat := f n
def apply_succ (n : Nat) : Nat := app_fun Nat.succ n
def nested_lambda : Nat -> Nat := fun x => (fun y : Nat => y + 1) x
def pair_type : Type := Prod Nat Nat
def prop_function : Prop -> Prop := fun P => P
"#
    ),
    corpus_file!(
        "basic_defs_08",
        "basic-defs",
        r#"def nat_pred_or_zero (n : Nat) : Nat := match n with | 0 => 0 | m + 1 => m
def nat_is_zero (n : Nat) : Bool := match n with | 0 => true | _ => false
def nat_plus_five (n : Nat) : Nat := n + 5
def nat_identity_fun : Nat -> Nat := fun n => n
theorem nat_plus_five_zero : nat_plus_five 0 = 5 := rfl
"#
    ),
    corpus_file!(
        "basic_theorems_01",
        "basic-theorems",
        r#"theorem thm_true_intro : True := True.intro
theorem thm_eq_zero : 0 = 0 := rfl
theorem thm_nat_id (n : Nat) : n = n := rfl
def thm_anchor_01 : Nat := 0
#print Nat
"#
    ),
    corpus_file!(
        "basic_theorems_02",
        "basic-theorems",
        r#"theorem thm_imp_id : True -> True := fun h => h
theorem thm_and_left : True -> True -> True := fun h _ => h
theorem thm_forall_id : forall n : Nat, n = n := fun n => rfl
def thm_anchor_02 : Prop := True
#check thm_imp_id
"#
    ),
    corpus_file!(
        "basic_theorems_03",
        "basic-theorems",
        r#"theorem thm_and_intro : True ∧ True := And.intro True.intro True.intro
theorem thm_and_swap : True ∧ True -> True ∧ True := fun h => And.intro h.2 h.1
theorem thm_eq_self (n : Nat) : n = n := Eq.trans rfl rfl
def thm_anchor_03 : Nat := 1
#check thm_and_intro
"#
    ),
    corpus_file!(
        "basic_theorems_04",
        "basic-theorems",
        r#"variable (A : Type)
theorem thm_poly_id (x : A) : x = x := rfl
theorem thm_poly_keep (x y : A) : x = x := rfl
def thm_anchor_04 : Type := A
#check thm_poly_id
"#
    ),
    corpus_file!(
        "basic_theorems_05",
        "basic-theorems",
        r#"theorem thm_eq_refl_nat (n : Nat) : n = n := rfl
theorem thm_eq_refl_bool (b : Bool) : b = b := rfl
theorem thm_arrow (f : Nat -> Nat) (n : Nat) : f n = f n := rfl
def thm_anchor_05 : Nat := 5
#print thm_eq_refl_nat
"#
    ),
    corpus_file!(
        "basic_theorems_06",
        "basic-theorems",
        r#"theorem thm_let_eq (n : Nat) : (let m := n; m) = n := rfl
theorem thm_lambda_eq (n : Nat) : (fun x : Nat => x) n = n := rfl
theorem thm_prod_refl (p : Prod Nat Nat) : p = p := rfl
def thm_anchor_06 : Nat := 6
#check thm_lambda_eq
"#
    ),
    corpus_file!(
        "basic_theorems_07",
        "basic-theorems",
        r#"theorem thm_true_arrow : True -> True := fun h => h
theorem thm_eq_succ : Nat.succ 0 = 1 := rfl
theorem thm_bool_cases : true = true := rfl
def thm_anchor_07 : Nat := 7
#print thm_eq_succ
"#
    ),
    corpus_file!(
        "basic_theorems_08",
        "basic-theorems",
        r#"theorem thm_keep_left (a b : Nat) : a = a := rfl
theorem thm_keep_right (a b : Nat) : b = b := rfl
theorem thm_prop_id (P : Prop) (h : P) : P := h
def thm_anchor_08 : Nat := 8
#check thm_prop_id
"#
    ),
    corpus_file!(
        "structures_inductives_01",
        "structures-inductives",
        r#"structure Point where
  x : Nat
  y : Nat
def point_origin : Point := { x := 0, y := 0 }
def point_swap (p : Point) : Point := { x := p.y, y := p.x }
"#
    ),
    corpus_file!(
        "structures_inductives_02",
        "structures-inductives",
        r#"structure Box (A : Type) where
  val : A
def boxedNat : Box Nat := { val := 3 }
def unboxNat (b : Box Nat) : Nat := b.val
theorem boxedNat_val : boxedNat.val = 3 := rfl
"#
    ),
    corpus_file!(
        "structures_inductives_03",
        "structures-inductives",
        r#"inductive Flag
| on
| off
def flipFlag (f : Flag) : Flag := match f with | Flag.on => Flag.off | Flag.off => Flag.on
theorem flipFlag_on : flipFlag Flag.on = Flag.off := rfl
"#
    ),
    corpus_file!(
        "structures_inductives_04",
        "structures-inductives",
        r#"inductive TinyNat
| zero
| succ (n : TinyNat)
def tinyPred (n : TinyNat) : TinyNat := match n with | TinyNat.zero => TinyNat.zero | TinyNat.succ m => m
theorem tinyPred_zero : tinyPred TinyNat.zero = TinyNat.zero := rfl
"#
    ),
    corpus_file!(
        "structures_inductives_05",
        "structures-inductives",
        r#"structure PairBox where
  left : Nat
  right : Nat
def pairBoxAnon : PairBox := ⟨1, 2⟩
theorem pairBox_left : pairBoxAnon.left = 1 := rfl
"#
    ),
    corpus_file!(
        "structures_inductives_06",
        "structures-inductives",
        r#"inductive MyList
| nil
| cons (head : Nat) (tail : MyList)
def myListHead (xs : MyList) : Nat := match xs with | MyList.nil => 0 | MyList.cons h _ => h
theorem myListHead_nil : myListHead MyList.nil = 0 := rfl
"#
    ),
    corpus_file!(
        "structures_inductives_07",
        "structures-inductives",
        r#"structure SizedVec where
  len : Nat
  data : Nat
def mkSizedVec : SizedVec := { len := 1, data := 42 }
theorem sizedVec_len : mkSizedVec.len = 1 := rfl
"#
    ),
    corpus_file!(
        "structures_inductives_08",
        "structures-inductives",
        r#"inductive Toggle
| yes
| no
def toggleToBool (t : Toggle) : Bool := match t with | Toggle.yes => true | Toggle.no => false
theorem toggleToBool_yes : toggleToBool Toggle.yes = true := rfl
"#
    ),
    corpus_file!(
        "classes_instances_01",
        "classes-instances",
        r#"class HasDefault (A : Type) where
  default : A
instance : HasDefault Nat where
  default := 0
def class_anchor_01 : Nat := 0
"#
    ),
    corpus_file!(
        "classes_instances_02",
        "classes-instances",
        r#"class HasBool (A : Type) where
  flag : A -> Bool
instance : HasBool Nat where
  flag := fun _ => true
def class_anchor_02 : Nat := 1
"#
    ),
    corpus_file!(
        "classes_instances_03",
        "classes-instances",
        r#"class WrapDefault (A : Type) where
  value : A
def useWrapDefault {A : Type} [WrapDefault A] : A := WrapDefault.value
instance : WrapDefault Nat where
  value := 7
theorem useWrapDefault_nat : useWrapDefault = (7 : Nat) := rfl
"#
    ),
    corpus_file!(
        "classes_instances_04",
        "classes-instances",
        r#"class TinyClass (A : Type) where
  witness : A
instance instTinyNat : TinyClass _ where
  witness := 9
def class_anchor_04 : Nat := 4
"#
    ),
    corpus_file!(
        "classes_instances_05",
        "classes-instances",
        r#"structure WrappedNat where
  val : Nat
class HasWrapped (A : Type) where
  get : A -> Nat
instance : HasWrapped WrappedNat where
  get := fun w => w.val
"#
    ),
    corpus_file!(
        "classes_instances_06",
        "classes-instances",
        r#"structure DefaultBox where
  val : Nat
class HasBoxDefault (A : Type) where
  default : A
instance : HasBoxDefault DefaultBox where
  default := ⟨42⟩
"#
    ),
    corpus_file!(
        "classes_instances_07",
        "classes-instances",
        r#"structure LiteralBox where
  val : Nat
class HasLiteralDefault (A : Type) where
  default : A
instance : HasLiteralDefault LiteralBox where
  default := { val := 11 }
"#
    ),
    corpus_file!(
        "classes_instances_08",
        "classes-instances",
        r#"class BaseZero (A : Type) where
  zero : A
class AddZero (A : Type) extends BaseZero A where
  add : A -> A -> A
instance : AddZero Nat where
  zero := 0
  add := Nat.add
"#
    ),
    corpus_file!(
        "imports_01",
        "imports",
        r#"import Mathlib
def imported_full_nat : Nat := 0
theorem imported_full_nat_rfl : imported_full_nat = 0 := rfl
#check Nat
#print Nat
"#
    ),
    corpus_file!(
        "imports_02",
        "imports",
        r#"import Mathlib.Data.Real.Basic
def imported_real_anchor : Nat := 1
theorem imported_real_anchor_rfl : imported_real_anchor = 1 := rfl
#check Nat
#print imported_real_anchor
"#
    ),
    corpus_file!(
        "imports_03",
        "imports",
        r#"import Mathlib.NumberTheory.Basic
def imported_number_anchor : Nat := 2
theorem imported_number_anchor_rfl : imported_number_anchor = 2 := rfl
#check Nat
#print imported_number_anchor
"#
    ),
    corpus_file!(
        "imports_04",
        "imports",
        r#"import Mathlib.Algebra.Ring.Basic
def imported_ring_anchor : Nat := 3
theorem imported_ring_anchor_rfl : imported_ring_anchor = 3 := rfl
#check Nat
#print imported_ring_anchor
"#
    ),
    corpus_file!(
        "imports_05",
        "imports",
        r#"import Mathlib.Algebra.Field.Basic
def imported_field_anchor : Nat := 4
theorem imported_field_anchor_rfl : imported_field_anchor = 4 := rfl
#check Nat
#print imported_field_anchor
"#
    ),
    corpus_file!(
        "imports_06",
        "imports",
        r#"import Mathlib.LinearAlgebra.Basic
def imported_linear_anchor : Nat := 5
theorem imported_linear_anchor_rfl : imported_linear_anchor = 5 := rfl
#check Nat
#print imported_linear_anchor
"#
    ),
    corpus_file!(
        "imports_07",
        "imports",
        r#"import Mathlib.MeasureTheory.Measure.MeasureSpace
def imported_measure_anchor : Nat := 6
theorem imported_measure_anchor_rfl : imported_measure_anchor = 6 := rfl
#check Nat
#print imported_measure_anchor
"#
    ),
    corpus_file!(
        "imports_08",
        "imports",
        r#"import Mathlib.Geometry.Euclidean.Basic
open scoped EuclideanGeometry
def imported_geometry_anchor : Nat := 7
theorem imported_geometry_anchor_rfl : imported_geometry_anchor = 7 := rfl
#print imported_geometry_anchor
"#
    ),
    corpus_file!(
        "namespaces_sections_01",
        "namespaces-sections",
        r#"namespace CorpusNsOne
def value : Nat := 0
theorem value_rfl : value = 0 := rfl
end CorpusNsOne
#print CorpusNsOne.value
"#
    ),
    corpus_file!(
        "namespaces_sections_02",
        "namespaces-sections",
        r#"namespace CorpusOuter
namespace Inner
def nestedValue : Nat := 1
end Inner
end CorpusOuter
"#
    ),
    corpus_file!(
        "namespaces_sections_03",
        "namespaces-sections",
        r#"section
variable (n : Nat)
def addLocal (m : Nat) : Nat := m + n
theorem addLocal_self : addLocal n = n + n := rfl
end
"#
    ),
    corpus_file!(
        "namespaces_sections_04",
        "namespaces-sections",
        r#"section
variable (A : Type) (x y : A)
def chooseSection : A := x
theorem chooseSection_eq : chooseSection A x y = x := rfl
end
"#
    ),
    corpus_file!(
        "namespaces_sections_05",
        "namespaces-sections",
        r#"universe u
def universeId (A : Type u) : Type u := A
def universeKeep (A : Type u) (x : A) : A := x
theorem universeId_rfl (A : Type u) : universeId A = A := rfl
#print universeId
"#
    ),
    corpus_file!(
        "namespaces_sections_06",
        "namespaces-sections",
        r#"universe u v
def universeLeft (A : Type u) (B : Type v) : Type u := A
def universeRight (A : Type u) (B : Type v) : Type v := B
theorem universeLeft_rfl (A : Type u) (B : Type v) : universeLeft A B = A := rfl
#check universeRight
"#
    ),
    corpus_file!(
        "namespaces_sections_07",
        "namespaces-sections",
        r#"open scoped Nat
def scopedNatValue : Nat := 0
theorem scopedNatValue_rfl : scopedNatValue = 0 := rfl
#check Nat.succ
#print scopedNatValue
"#
    ),
    corpus_file!(
        "namespaces_sections_08",
        "namespaces-sections",
        r#"namespace OpenNs
def openedValue : Nat := 2
end OpenNs
open OpenNs
theorem openedValue_rfl : openedValue = 2 := rfl
"#
    ),
    corpus_file!(
        "macros_notations_01",
        "macros-notations",
        r#"macro_rules | `(myId $x) => `($x)
def macro_rules_anchor_01 : Nat := 0
theorem macro_rules_anchor_01_rfl : macro_rules_anchor_01 = 0 := rfl
#check Nat
#print Nat
"#
    ),
    corpus_file!(
        "macros_notations_02",
        "macros-notations",
        r#"macro_rules | `(wrapNat $x) => `($x)
def macro_rules_anchor_02 : Nat := 1
theorem macro_rules_anchor_02_rfl : macro_rules_anchor_02 = 1 := rfl
#check macro_rules_anchor_02
#print Nat
"#
    ),
    corpus_file!(
        "macros_notations_03",
        "macros-notations",
        r#"declare_syntax_cat corpusCat
def syntax_cat_anchor : Nat := 2
theorem syntax_cat_anchor_rfl : syntax_cat_anchor = 2 := rfl
#check Nat
#print syntax_cat_anchor
"#
    ),
    corpus_file!(
        "macros_notations_04",
        "macros-notations",
        r#"infixl:65 " +++ " => fun x y => x
def notation_infixl_left : Nat := 3
theorem notation_infixl_left_rfl : notation_infixl_left = 3 := rfl
#check Nat
#print notation_infixl_left
"#
    ),
    corpus_file!(
        "macros_notations_05",
        "macros-notations",
        r#"infixr:70 " <+> " => fun x y => y
def notation_infixr_right : Nat := 4
theorem notation_infixr_right_rfl : notation_infixr_right = 4 := rfl
#check Nat
#print notation_infixr_right
"#
    ),
    corpus_file!(
        "macros_notations_06",
        "macros-notations",
        r#"prefix:100 "!!!" => fun x => x
def notation_prefix_anchor : Nat := 5
theorem notation_prefix_anchor_rfl : notation_prefix_anchor = 5 := rfl
#check Nat
#print notation_prefix_anchor
"#
    ),
    corpus_file!(
        "macros_notations_07",
        "macros-notations",
        r#"postfix:100 "?" => fun x => x
def notation_postfix_anchor : Nat := 6
theorem notation_postfix_anchor_rfl : notation_postfix_anchor = 6 := rfl
#check Nat
#print notation_postfix_anchor
"#
    ),
    corpus_file!(
        "macros_notations_08",
        "macros-notations",
        r#"notation a " ++! " b => a
def notation_general_anchor : Nat := 7
theorem notation_general_anchor_rfl : notation_general_anchor = 7 := rfl
#check Nat
#print notation_general_anchor
"#
    ),
    corpus_file!(
        "tactics_01",
        "tactics",
        r#"theorem tactic_rfl_zero : 0 = 0 := by
  rfl
theorem tactic_rfl_id (n : Nat) : (fun x : Nat => x) n = n := by
  rfl
#print tactic_rfl_zero
"#
    ),
    corpus_file!(
        "tactics_02",
        "tactics",
        r#"theorem tactic_exact_true : True := by
  exact True.intro
theorem tactic_exact_rfl (n : Nat) : n = n := by
  exact rfl
#print tactic_exact_true
"#
    ),
    corpus_file!(
        "tactics_03",
        "tactics",
        r#"theorem tactic_assumption_true (h : True) : True := by
  assumption
theorem tactic_assumption_eq (n : Nat) (h : n = n) : n = n := by
  assumption
#print tactic_assumption_true
"#
    ),
    corpus_file!(
        "tactics_04",
        "tactics",
        r#"theorem tactic_constructor_and : True ∧ True := by
  constructor
  exact True.intro
  exact True.intro
#print tactic_constructor_and
"#
    ),
    corpus_file!(
        "tactics_05",
        "tactics",
        r#"theorem tactic_simp_beta : (fun x : Nat => x) 0 = 0 := by
  simp
def tactic_simp_anchor : Nat := 1
theorem tactic_simp_anchor_rfl : tactic_simp_anchor = 1 := rfl
#print tactic_simp_beta
"#
    ),
    corpus_file!(
        "tactics_06",
        "tactics",
        r#"def simpMarked : Nat := 1
@[simp] theorem simpMarked_eq : simpMarked = 1 := rfl
theorem tactic_simp_marked : simpMarked = 1 := by
  simp
#print tactic_simp_marked
"#
    ),
    corpus_file!(
        "tactics_07",
        "tactics",
        r#"theorem tactic_mathverse_contra (h : 2 <= 1) : False := by
  mathverse
def tactic_mathverse_anchor : Nat := 2
theorem tactic_mathverse_anchor_rfl : tactic_mathverse_anchor = 2 := rfl
#print tactic_mathverse_anchor
"#
    ),
    corpus_file!(
        "tactics_08",
        "tactics",
        r#"theorem tactic_mathverse_linear (n : Nat) (h : n + 1 <= n) : False := by
  mathverse
def tactic_mathverse_linear_anchor : Nat := 3
theorem tactic_mathverse_linear_anchor_rfl : tactic_mathverse_linear_anchor = 3 := rfl
#print tactic_mathverse_linear_anchor
"#
    ),
    corpus_file!(
        "pattern_recursion_01",
        "pattern-recursion",
        r#"def isZero : Nat -> Bool
  | 0 => true
  | _ => false
theorem isZero_zero : isZero 0 = true := rfl
#print isZero
"#
    ),
    corpus_file!(
        "pattern_recursion_02",
        "pattern-recursion",
        r#"def predOrZero : Nat -> Nat
  | 0 => 0
  | n + 1 => n
theorem predOrZero_zero : predOrZero 0 = 0 := rfl
#print predOrZero
"#
    ),
    corpus_file!(
        "pattern_recursion_03",
        "pattern-recursion",
        r#"def sumUpTo : Nat -> Nat
  | 0 => 0
  | n + 1 => sumUpTo n + (n + 1)
theorem sumUpTo_zero : sumUpTo 0 = 0 := rfl
#print sumUpTo
"#
    ),
    corpus_file!(
        "pattern_recursion_04",
        "pattern-recursion",
        r#"def matchNat (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | m + 1 => m
theorem matchNat_zero : matchNat 0 = 0 := rfl
"#
    ),
    corpus_file!(
        "pattern_recursion_05",
        "pattern-recursion",
        r#"def outerWhere (n : Nat) : Nat :=
  helper n
where
  helper (m : Nat) : Nat := m + 1
#print outerWhere
"#
    ),
    corpus_file!(
        "pattern_recursion_06",
        "pattern-recursion",
        r#"def countDown (n : Nat) : Nat :=
  go n
where
  go : Nat -> Nat
  | 0 => 0
  | m + 1 => go m
"#
    ),
    corpus_file!(
        "pattern_recursion_07",
        "pattern-recursion",
        r#"inductive TinyFlag
| yes
| no
def tinyFlagToNat (f : TinyFlag) : Nat := match f with | TinyFlag.yes => 1 | TinyFlag.no => 0
theorem tinyFlagToNat_yes : tinyFlagToNat TinyFlag.yes = 1 := rfl
"#
    ),
    corpus_file!(
        "pattern_recursion_08",
        "pattern-recursion",
        r#"def natListLen : List Nat -> Nat
  | List.nil => 0
  | List.cons _ xs => natListLen xs + 1
theorem natListLen_nil : natListLen List.nil = 0 := rfl
#print natListLen
"#
    ),
    corpus_file!(
        "misc_commands_01",
        "misc-commands",
        r#"set_option pp.all
def option_anchor : Nat := 0
theorem option_anchor_rfl : option_anchor = 0 := rfl
#eval Nat.zero
#print option_anchor
"#
    ),
    corpus_file!(
        "misc_commands_02",
        "misc-commands",
        r#"example : Nat := 0
def example_anchor : Nat := 1
theorem example_anchor_rfl : example_anchor = 1 := rfl
#check example_anchor
#print example_anchor
"#
    ),
    corpus_file!(
        "misc_commands_03",
        "misc-commands",
        r#"axiom misc_axiom_nat : Nat
theorem misc_axiom_eq : misc_axiom_nat = misc_axiom_nat := rfl
def misc_axiom_use : Nat := misc_axiom_nat
#check misc_axiom_nat
#print misc_axiom_use
"#
    ),
    corpus_file!(
        "misc_commands_04",
        "misc-commands",
        r#"opaque misc_hidden_nat : Nat := 2
theorem misc_hidden_nat_rfl : misc_hidden_nat = misc_hidden_nat := rfl
def misc_hidden_use : Nat := misc_hidden_nat
#check misc_hidden_nat
#print misc_hidden_use
"#
    ),
    corpus_file!(
        "misc_commands_05",
        "misc-commands",
        r#"abbrev SmallNat := Nat
def smallNatValue : SmallNat := 3
theorem smallNatValue_rfl : smallNatValue = 3 := rfl
#check SmallNat
#print smallNatValue
"#
    ),
    corpus_file!(
        "misc_commands_06",
        "misc-commands",
        r#"def attrTarget : Nat := 4
attribute [simp] attrTarget
theorem attrTarget_rfl : attrTarget = 4 := rfl
#check attrTarget
#print attrTarget
"#
    ),
    corpus_file!(
        "misc_commands_07",
        "misc-commands",
        r#"def doIdNat : Id Nat := do
  let x := 5
  pure x
theorem doIdNat_rfl : doIdNat = 5 := rfl
#print doIdNat
"#
    ),
    corpus_file!(
        "misc_commands_08",
        "misc-commands",
        r#"theorem calc_refl_nat (n : Nat) : n = n := by
  calc
    n = n := rfl
def calc_anchor : Nat := 6
#print calc_anchor
"#
    ),
];

fn panic_message(payload: Box<dyn Any + Send>) -> String {
    let payload = &*payload;
    if let Some(message) = payload.downcast_ref::<String>() {
        return message.clone();
    }
    if let Some(message) = payload.downcast_ref::<&'static str>() {
        return (*message).to_string();
    }
    "unknown panic payload".to_string()
}

fn run_file(file: CorpusFile) -> Result<(), CorpusError> {
    match catch_unwind(AssertUnwindSafe(|| {
        let decls = parse_file(file.source).map_err(|e| CorpusError {
            file: file.name,
            category: file.category,
            kind: "parse",
            message: format!("{e}"),
        })?;

        let mut env = phase1_corpus_common::phase1_elab_env();
        let mut file_ctx = FileContext::new();

        for (index, decl) in decls.iter().enumerate() {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register(&mut env, &processed).map_err(|e| CorpusError {
                file: file.name,
                category: file.category,
                kind: "elab",
                message: format!("declaration {index}: {e}"),
            })?;
        }

        Ok(())
    })) {
        Ok(result) => result,
        Err(payload) => Err(CorpusError {
            file: file.name,
            category: file.category,
            kind: "panic",
            message: panic_message(payload),
        }),
    }
}

fn run_corpus() -> CorpusMeasurement {
    let mut errors = Vec::new();
    let mut passed = 0;

    for file in CORPUS_FILES {
        match run_file(*file) {
            Ok(()) => passed += 1,
            Err(error) => errors.push(error),
        }
    }

    let total = CORPUS_FILES.len();
    let failed = errors.len();

    CorpusMeasurement {
        total,
        passed,
        failed,
        errors,
    }
}

fn report_measurement(measurement: &CorpusMeasurement) {
    let success_rate = if measurement.total == 0 {
        0.0
    } else {
        (measurement.passed as f64 / measurement.total as f64) * 100.0
    };

    let mut corpus_categories = BTreeMap::<&'static str, usize>::new();
    for file in CORPUS_FILES {
        *corpus_categories.entry(file.category).or_default() += 1;
    }

    let mut failure_kinds = BTreeMap::<&'static str, usize>::new();
    let mut failure_categories = BTreeMap::<&'static str, usize>::new();
    for error in &measurement.errors {
        *failure_kinds.entry(error.kind).or_default() += 1;
        *failure_categories.entry(error.category).or_default() += 1;
    }

    println!("=== Lean 4 Representative Corpus Measurement ===");
    println!("Files: {}", measurement.total);
    println!("Passed: {}", measurement.passed);
    println!("Failed: {}", measurement.failed);
    println!("Success rate: {:.1}%", success_rate);
    println!();
    println!("Corpus categories:");
    for (category, count) in corpus_categories {
        println!("  {category}: {count}");
    }
    println!();
    println!("Failure kinds:");
    if failure_kinds.is_empty() {
        println!("  none");
    } else {
        for (kind, count) in failure_kinds {
            println!("  {kind}: {count}");
        }
    }
    println!();
    println!("Failures by corpus category:");
    if failure_categories.is_empty() {
        println!("  none");
    } else {
        for (category, count) in failure_categories {
            println!("  {category}: {count}");
        }
    }

    if !measurement.errors.is_empty() {
        println!();
        println!("Failure details:");
        for error in &measurement.errors {
            println!("  [{}:{}] {}", error.category, error.kind, error.file);
            println!("    {}", error.message);
        }
    }
}

#[test]
fn measure_corpus_success_rate() {
    assert_eq!(
        CORPUS_FILES.len(),
        80,
        "Representative corpus drift: expected 80 snippets"
    );

    let measurement = run_corpus();
    assert_eq!(measurement.total, CORPUS_FILES.len());
    assert_eq!(measurement.passed + measurement.failed, measurement.total);
    report_measurement(&measurement);
}

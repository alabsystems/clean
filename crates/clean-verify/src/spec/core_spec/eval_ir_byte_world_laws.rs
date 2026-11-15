// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked activation-world preservation for the actual byte evaluator.
//!
//! The premises are the existing pre-state checks, not post-state guards.
//! Owner-list and allocation-list induction establish fresh insertion and
//! retirement/removal. Frame-shape rules then preserve the exact world check
//! used by every machine step. They do not establish provider fidelity, heap
//! disjointness, accessibility, or arbitrary instruction preservation.

use crate::spec::{SpecError, Specification};

const BOOL_FALSE_TRUE: &str = r"def ir_byte_world_false_true_v1
  (h : @Eq Bool Bool.false Bool.true) : False :=
@Eq.subst Bool (fun (b : Bool) => @Bool.rec (fun (_ : Bool) => Prop) True False b)
  Bool.false Bool.true h True.intro";

const AND_LEFT: &str = r"def ir_byte_world_and_left_v1 (a b : Bool)
  (h : @Eq Bool (Bool.and a b) Bool.true) : @Eq Bool a Bool.true :=
@Bool.rec (fun (x : Bool) => @Eq Bool (Bool.and x b) Bool.true -> @Eq Bool x Bool.true)
  (fun (h : @Eq Bool Bool.false Bool.true) => h)
  (fun (_ : @Eq Bool b Bool.true) => @Eq.refl Bool Bool.true) a h";

const AND_RIGHT: &str = r"def ir_byte_world_and_right_v1 (a b : Bool)
  (h : @Eq Bool (Bool.and a b) Bool.true) : @Eq Bool b Bool.true :=
@Bool.rec (fun (x : Bool) => @Eq Bool (Bool.and x b) Bool.true -> @Eq Bool b Bool.true)
  (fun (h : @Eq Bool Bool.false Bool.true) => @False.elim (@Eq Bool b Bool.true)
    (ir_byte_world_false_true_v1 h))
  (fun (h : @Eq Bool b Bool.true) => h) a h";

const AND_INTRO: &str = r"def ir_byte_world_and_intro_v1 (a b : Bool)
  (ha : @Eq Bool a Bool.true) (hb : @Eq Bool b Bool.true) :
@Eq Bool (Bool.and a b) Bool.true :=
@Eq.trans Bool (Bool.and a b) b Bool.true
  (ir_eq_cong Bool Bool (fun (x : Bool) => Bool.and x b) a Bool.true ha) hb";

const OR_FALSE: &str = r"def ir_byte_world_or_false_v1 (a b : Bool)
  (ha : @Eq Bool a Bool.false) (hb : @Eq Bool b Bool.false) :
@Eq Bool (Bool.or a b) Bool.false :=
@Eq.trans Bool (Bool.or a b) b Bool.false
  (ir_eq_cong Bool Bool (fun (x : Bool) => Bool.or x b) a Bool.false ha) hb";

const LT_RAISE_WALK: &str = r"def ir_byte_world_lt_raise_walk_v1 (a b : Nat)
  (h : @Eq Bool (ir_nat_ltb_walk a b) Bool.true) :
@Eq Bool (ir_nat_ltb_walk a (Nat.succ b)) Bool.true :=
@Nat.rec
  (fun (x : Nat) => forall (y : Nat), @Eq Bool (ir_nat_ltb_walk x y) Bool.true ->
    @Eq Bool (ir_nat_ltb_walk x (Nat.succ y)) Bool.true)
  (fun (y : Nat) (_ : @Eq Bool (ir_nat_ltb_walk 0 y) Bool.true) => @Eq.refl Bool Bool.true)
  (fun (x : Nat) (ih : forall (y : Nat), @Eq Bool (ir_nat_ltb_walk x y) Bool.true ->
    @Eq Bool (ir_nat_ltb_walk x (Nat.succ y)) Bool.true) =>
    fun (y : Nat) => @Nat.rec
      (fun (z : Nat) => @Eq Bool (ir_nat_ltb_walk (Nat.succ x) z) Bool.true ->
        @Eq Bool (ir_nat_ltb_walk (Nat.succ x) (Nat.succ z)) Bool.true)
      (fun (bad : @Eq Bool Bool.false Bool.true) =>
        @False.elim (@Eq Bool (ir_nat_ltb_walk (Nat.succ x) 1) Bool.true)
          (ir_byte_world_false_true_v1 bad))
      (fun (z : Nat) (_ : @Eq Bool (ir_nat_ltb_walk (Nat.succ x) z) Bool.true ->
        @Eq Bool (ir_nat_ltb_walk (Nat.succ x) (Nat.succ z)) Bool.true) =>
        fun (less : @Eq Bool (ir_nat_ltb_walk x z) Bool.true) => ih z less) y)
  a b h";

const LT_RAISE: &str = r"def ir_byte_world_lt_raise_v1 (a b : Nat)
  (h : @Eq Bool (ir_nat_ltb a b) Bool.true) : @Eq Bool (ir_nat_ltb a (Nat.succ b)) Bool.true :=
@Eq.trans Bool (ir_nat_ltb a (Nat.succ b)) (ir_nat_ltb_walk a (Nat.succ b)) Bool.true
  (ir_nat_ltb_walk_eq a (Nat.succ b))
  (ir_byte_world_lt_raise_walk_v1 a b
    (@Eq.trans Bool (ir_nat_ltb_walk a b) (ir_nat_ltb a b) Bool.true
      (@Eq.symm Bool (ir_nat_ltb a b) (ir_nat_ltb_walk a b) (ir_nat_ltb_walk_eq a b)) h))";

const LT_NE_WALK: &str = r"def ir_byte_world_lt_ne_walk_v1 (a b : Nat)
  (h : @Eq Bool (ir_nat_ltb_walk a b) Bool.true) : @Eq Bool (ir_nat_eqb_walk a b) Bool.false :=
@Nat.rec
  (fun (x : Nat) => forall (y : Nat), @Eq Bool (ir_nat_ltb_walk x y) Bool.true ->
    @Eq Bool (ir_nat_eqb_walk x y) Bool.false)
  (fun (y : Nat) => @Nat.rec
    (fun (z : Nat) => @Eq Bool (ir_nat_ltb_walk 0 z) Bool.true -> @Eq Bool (ir_nat_eqb_walk 0 z) Bool.false)
    (fun (bad : @Eq Bool Bool.false Bool.true) => @False.elim (@Eq Bool Bool.true Bool.false)
      (ir_byte_world_false_true_v1 bad))
    (fun (z : Nat) (_ : @Eq Bool (ir_nat_ltb_walk 0 z) Bool.true -> @Eq Bool (ir_nat_eqb_walk 0 z) Bool.false) =>
      fun (_ : @Eq Bool Bool.true Bool.true) => @Eq.refl Bool Bool.false) y)
  (fun (x : Nat) (ih : forall (y : Nat), @Eq Bool (ir_nat_ltb_walk x y) Bool.true ->
    @Eq Bool (ir_nat_eqb_walk x y) Bool.false) =>
    fun (y : Nat) => @Nat.rec
      (fun (z : Nat) => @Eq Bool (ir_nat_ltb_walk (Nat.succ x) z) Bool.true ->
        @Eq Bool (ir_nat_eqb_walk (Nat.succ x) z) Bool.false)
      (fun (_ : @Eq Bool Bool.false Bool.true) => @Eq.refl Bool Bool.false)
      (fun (z : Nat) (_ : @Eq Bool (ir_nat_ltb_walk (Nat.succ x) z) Bool.true ->
        @Eq Bool (ir_nat_eqb_walk (Nat.succ x) z) Bool.false) =>
        fun (less : @Eq Bool (ir_nat_ltb_walk x z) Bool.true) => ih z less) y)
  a b h";

const LT_NE: &str = r"def ir_byte_world_lt_ne_v1 (a b : Nat)
  (h : @Eq Bool (ir_nat_ltb a b) Bool.true) : @Eq Bool (ir_nat_eqb a b) Bool.false :=
@Eq.trans Bool (ir_nat_eqb a b) (ir_nat_eqb_walk a b) Bool.false (ir_nat_eqb_walk_eq a b)
  (ir_byte_world_lt_ne_walk_v1 a b
    (@Eq.trans Bool (ir_nat_ltb_walk a b) (ir_nat_ltb a b) Bool.true
      (@Eq.symm Bool (ir_nat_ltb a b) (ir_nat_ltb_walk a b) (ir_nat_ltb_walk_eq a b)) h))";

const EQ_SUCC: &str = r"def ir_byte_world_eq_succ_v1 (a b : Nat) :
@Eq Bool (ir_nat_eqb (Nat.succ a) (Nat.succ b)) (ir_nat_eqb a b) :=
@Eq.trans Bool (ir_nat_eqb (Nat.succ a) (Nat.succ b)) (ir_nat_eqb_walk a b) (ir_nat_eqb a b)
  (ir_nat_eqb_walk_eq (Nat.succ a) (Nat.succ b))
  (@Eq.symm Bool (ir_nat_eqb a b) (ir_nat_eqb_walk a b) (ir_nat_eqb_walk_eq a b))";

fn and(a: &str, b: &str) -> String {
    format!("(Bool.and {a} {b})")
}

fn left(a: &str, b: &str, proof: &str) -> String {
    format!("(ir_byte_world_and_left_v1 {a} {b} {proof})")
}

fn right(a: &str, b: &str, proof: &str) -> String {
    format!("(ir_byte_world_and_right_v1 {a} {b} {proof})")
}

fn join(a: &str, b: &str, pa: &str, pb: &str) -> String {
    format!("(ir_byte_world_and_intro_v1 {a} {b} {pa} {pb})")
}

/// Small propositional proof generator, not an alternative memory evaluator.
/// Each truth-table leaf becomes an ordinary checked Bool.rec proof. The kernel
/// independently verifies all reductions and implications in the result.
#[derive(Clone)]
enum Boolean {
    Variable(usize),
    Not(Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
}

impl Boolean {
    fn render(&self, values: &[String]) -> String {
        match self {
            Self::Variable(i) => values[*i].clone(),
            Self::Not(a) => format!("(Bool.not {})", a.render(values)),
            Self::And(a, b) => and(&a.render(values), &b.render(values)),
            Self::Or(a, b) => format!("(Bool.or {} {})", a.render(values), b.render(values)),
        }
    }

    fn value(&self, values: &[bool]) -> bool {
        match self {
            Self::Variable(i) => values[*i],
            Self::Not(a) => !a.value(values),
            Self::And(a, b) => a.value(values) && b.value(values),
            Self::Or(a, b) => a.value(values) || b.value(values),
        }
    }
}

fn boolean_implication(name: &str, before: Boolean, after: Boolean) -> Result<String, SpecError> {
    const VARIABLES: [&str; 4] = ["live", "global", "same", "member"];
    fn proof(
        before: &Boolean,
        after: &Boolean,
        prefix: &mut Vec<bool>,
    ) -> Result<String, SpecError> {
        let mut values = VARIABLES
            .iter()
            .map(|v| (*v).into())
            .collect::<Vec<String>>();
        for (i, &value) in prefix.iter().enumerate() {
            values[i] = if value { "Bool.true" } else { "Bool.false" }.into();
        }
        let premise = format!("@Eq Bool {} Bool.true", before.render(&values));
        let goal = format!("@Eq Bool {} Bool.true", after.render(&values));
        if prefix.len() == VARIABLES.len() {
            let body = if after.value(prefix) {
                "@Eq.refl Bool Bool.true"
            } else if !before.value(prefix) {
                "h"
            } else {
                return Err(SpecError::TypeError(
                    "invalid Boolean implication candidate".into(),
                ));
            };
            return Ok(format!("(fun (h : {premise}) => {body})"));
        }
        let position = prefix.len();
        let variable = VARIABLES[position];
        let remaining = VARIABLES[position + 1..]
            .iter()
            .map(|v| format!("forall ({v} : Bool), "))
            .collect::<String>();
        prefix.push(false);
        let false_case = proof(before, after, prefix)?;
        prefix[position] = true;
        let true_case = proof(before, after, prefix)?;
        prefix.pop();
        Ok(format!(
            "(fun ({variable} : Bool) => @Bool.rec\n\
            (fun ({variable} : Bool) => {remaining}{premise} -> {goal})\n\
            {false_case} {true_case} {variable})"
        ))
    }
    let names = VARIABLES
        .iter()
        .map(|v| (*v).into())
        .collect::<Vec<String>>();
    Ok(format!(
        "def {name} (live global same member : Bool)\n\
        (h : @Eq Bool {} Bool.true) : @Eq Bool {} Bool.true :=\n\
        {} live global same member h",
        before.render(&names),
        after.render(&names),
        proof(&before, &after, &mut Vec::new())?
    ))
}

fn support_laws() -> Result<Vec<(&'static str, String)>, SpecError> {
    use Boolean::{And as A, Not as N, Or as O, Variable as V};
    let or = |a, b| O(Box::new(a), Box::new(b));
    let not = |a| N(Box::new(a));
    Ok(vec![
        (
            "ir_byte_world_support_push_v1",
            boolean_implication(
                "ir_byte_world_support_push_v1",
                or(not(V(0)), or(V(1), V(3))),
                or(not(V(0)), or(V(1), or(V(2), V(3)))),
            )?,
        ),
        (
            "ir_byte_world_support_pop_v1",
            boolean_implication(
                "ir_byte_world_support_pop_v1",
                or(not(V(0)), or(V(1), or(V(2), V(3)))),
                or(not(A(Box::new(V(0)), Box::new(not(V(2))))), or(V(1), V(3))),
            )?,
        ),
    ])
}

fn owners_row(next: &str) -> String {
    and(
        "(ir_nat_pos x)",
        &and(
            &format!("(ir_nat_ltb x {next})"),
            "(Bool.not (ir_byte_owner_member_v1 x tail))",
        ),
    )
}

fn owners_laws() -> Vec<(&'static str, String)> {
    let old_tail = "(ir_byte_owners_valid_v1 tail next)";
    let new_tail = "(ir_byte_owners_valid_v1 tail (Nat.succ next))";
    let old_row = owners_row("next");
    let tail_proof = left(old_tail, &old_row, "h");
    let row_proof = right(old_tail, &old_row, "h");
    let less_and_distinct = and(
        "(ir_nat_ltb x next)",
        "(Bool.not (ir_byte_owner_member_v1 x tail))",
    );
    let positive = left("(ir_nat_pos x)", &less_and_distinct, &row_proof);
    let rest = right("(ir_nat_pos x)", &less_and_distinct, &row_proof);
    let less = left(
        "(ir_nat_ltb x next)",
        "(Bool.not (ir_byte_owner_member_v1 x tail))",
        &rest,
    );
    let distinct = right(
        "(ir_nat_ltb x next)",
        "(Bool.not (ir_byte_owner_member_v1 x tail))",
        &rest,
    );
    let raised_row = join(
        "(ir_nat_pos x)",
        &and(
            "(ir_nat_ltb x (Nat.succ next))",
            "(Bool.not (ir_byte_owner_member_v1 x tail))",
        ),
        &positive,
        &join(
            "(ir_nat_ltb x (Nat.succ next))",
            "(Bool.not (ir_byte_owner_member_v1 x tail))",
            &format!("(ir_byte_world_lt_raise_v1 x next {less})"),
            &distinct,
        ),
    );
    vec![
        ("ir_byte_owners_tail_v1", "def ir_byte_owners_tail_v1 (owner : Nat) (owners : IRList Nat) (next : Nat)\n\
          (h : @Eq Bool (ir_byte_owners_valid_v1 (@IRList.cons Nat owner owners) next) Bool.true) :\n\
          @Eq Bool (ir_byte_owners_valid_v1 owners next) Bool.true :=\n\
          ir_byte_world_and_left_v1 (ir_byte_owners_valid_v1 owners next)\n\
            (Bool.and (ir_nat_pos owner) (Bool.and (ir_nat_ltb owner next) (Bool.not (ir_byte_owner_member_v1 owner owners)))) h".to_string()),
        ("ir_byte_owners_next_positive_v1", format!("def ir_byte_owners_next_positive_v1 (owners : IRList Nat) (next : Nat)\n\
          (h : @Eq Bool (ir_byte_owners_valid_v1 owners next) Bool.true) : @Eq Bool (ir_nat_pos next) Bool.true :=\n\
          @IRList.rec Nat (fun (xs : IRList Nat) => @Eq Bool (ir_byte_owners_valid_v1 xs next) Bool.true -> @Eq Bool (ir_nat_pos next) Bool.true)\n\
            (fun (h : @Eq Bool (ir_nat_pos next) Bool.true) => h)\n\
            (fun (x : Nat) (tail : IRList Nat) (ih : @Eq Bool {old_tail} Bool.true -> @Eq Bool (ir_nat_pos next) Bool.true) =>\n\
              fun (h : @Eq Bool (ir_byte_owners_valid_v1 (@IRList.cons Nat x tail) next) Bool.true) => ih {tail_proof}) owners h")),
        ("ir_byte_owners_fresh_v1", format!("def ir_byte_owners_fresh_v1 (owners : IRList Nat) (next : Nat)\n\
          (h : @Eq Bool (ir_byte_owners_valid_v1 owners next) Bool.true) : @Eq Bool (ir_byte_owner_member_v1 next owners) Bool.false :=\n\
          @IRList.rec Nat (fun (xs : IRList Nat) => @Eq Bool (ir_byte_owners_valid_v1 xs next) Bool.true -> @Eq Bool (ir_byte_owner_member_v1 next xs) Bool.false)\n\
            (fun (_ : @Eq Bool (ir_nat_pos next) Bool.true) => @Eq.refl Bool Bool.false)\n\
            (fun (x : Nat) (tail : IRList Nat) (ih : @Eq Bool {old_tail} Bool.true -> @Eq Bool (ir_byte_owner_member_v1 next tail) Bool.false) =>\n\
              fun (h : @Eq Bool (ir_byte_owners_valid_v1 (@IRList.cons Nat x tail) next) Bool.true) =>\n\
                ir_byte_world_or_false_v1 (ir_nat_eqb x next) (ir_byte_owner_member_v1 next tail)\n\
                  (ir_byte_world_lt_ne_v1 x next {less}) (ih {tail_proof})) owners h")),
        ("ir_byte_owners_raise_v1", format!("def ir_byte_owners_raise_v1 (owners : IRList Nat) (next : Nat)\n\
          (h : @Eq Bool (ir_byte_owners_valid_v1 owners next) Bool.true) : @Eq Bool (ir_byte_owners_valid_v1 owners (Nat.succ next)) Bool.true :=\n\
          @IRList.rec Nat (fun (xs : IRList Nat) => @Eq Bool (ir_byte_owners_valid_v1 xs next) Bool.true -> @Eq Bool (ir_byte_owners_valid_v1 xs (Nat.succ next)) Bool.true)\n\
            (fun (_ : @Eq Bool (ir_nat_pos next) Bool.true) => @Eq.refl Bool Bool.true)\n\
            (fun (x : Nat) (tail : IRList Nat) (ih : @Eq Bool {old_tail} Bool.true -> @Eq Bool {new_tail} Bool.true) =>\n\
              fun (h : @Eq Bool (ir_byte_owners_valid_v1 (@IRList.cons Nat x tail) next) Bool.true) => {}) owners h",
            join(new_tail, &owners_row("(Nat.succ next)"), &format!("(ih {tail_proof})"), &raised_row))),
        ("ir_byte_owners_push_v1", r"def ir_byte_owners_push_v1 (owners : IRList Nat) (next : Nat)
          (h : @Eq Bool (ir_byte_owners_valid_v1 owners next) Bool.true) :
          @Eq Bool (ir_byte_owners_valid_v1 (@IRList.cons Nat next owners) (Nat.succ next)) Bool.true :=
          ir_byte_world_and_intro_v1 (ir_byte_owners_valid_v1 owners (Nat.succ next))
            (Bool.and (ir_nat_pos next) (Bool.and (ir_nat_ltb next (Nat.succ next)) (Bool.not (ir_byte_owner_member_v1 next owners))))
            (ir_byte_owners_raise_v1 owners next h)
            (ir_byte_world_and_intro_v1 (ir_nat_pos next)
              (Bool.and (ir_nat_ltb next (Nat.succ next)) (Bool.not (ir_byte_owner_member_v1 next owners)))
              (ir_byte_owners_next_positive_v1 owners next h)
              (ir_byte_world_and_intro_v1 (ir_nat_ltb next (Nat.succ next)) (Bool.not (ir_byte_owner_member_v1 next owners))
                (ir_byte_ltb_of_lt_v1 next (Nat.succ next) (Nat.le_refl (Nat.succ next)))
                (ir_eq_cong Bool Bool (fun (b : Bool) => Bool.not b)
                  (ir_byte_owner_member_v1 next owners) Bool.false (ir_byte_owners_fresh_v1 owners next h))))".into()),
    ]
}

fn memory_law(pop: bool) -> (&'static str, String) {
    let name = if pop {
        "ir_byte_memory_owners_pop_v1"
    } else {
        "ir_byte_memory_owners_push_v1"
    };
    let before_owners = if pop {
        "(@IRList.cons Nat owner owners)"
    } else {
        "owners"
    };
    let after_owners = if pop {
        "owners"
    } else {
        "(@IRList.cons Nat next owners)"
    };
    let after_next = if pop { "next" } else { "(Nat.succ next)" };
    let old = |xs: &str| {
        format!("(ir_byte_memory_owners_v1 (IRByteMemoryV1.mk {xs} (ir_byte_mem_bytes_v1 mem) (ir_byte_mem_next_v1 mem)) {before_owners} next)")
    };
    let new = |xs: &str| {
        let xs = if pop {
            format!("(ir_byte_retire_allocs_v1 owner {xs})")
        } else {
            xs.into()
        };
        format!("(ir_byte_memory_owners_v1 (IRByteMemoryV1.mk {xs} (ir_byte_mem_bytes_v1 mem) (ir_byte_mem_next_v1 mem)) {after_owners} {after_next})")
    };
    let live = "(ir_byte_alloc_live_v1 a)";
    let global = "(ir_nat_eqb (ir_byte_alloc_owner_v1 a) 0)";
    let member = "(ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 a) owners)";
    let same = format!(
        "(ir_nat_eqb {} (ir_byte_alloc_owner_v1 a))",
        if pop { "owner" } else { "next" }
    );
    let old_member = if pop {
        format!("(Bool.or {same} {member})")
    } else {
        member.into()
    };
    let old_support = format!("(Bool.or (Bool.not {live}) (Bool.or {global} {old_member}))");
    let new_support = if pop {
        format!(
            "(Bool.or (Bool.not (Bool.and {live} (Bool.not {same}))) (Bool.or {global} {member}))"
        )
    } else {
        format!("(Bool.or (Bool.not {live}) (Bool.or {global} (Bool.or {same} {member})))")
    };
    let valid = "(ir_byte_alloc_valid_v1 a)";
    let bound = "(ir_nat_ltb (ir_byte_alloc_owner_v1 a) next)";
    let raised_bound = format!("(ir_nat_ltb (ir_byte_alloc_owner_v1 a) {after_next})");
    let old_row = and(valid, &and(bound, &old_support));
    let row_proof = right(&old("tail"), &old_row, "h");
    let valid_proof = left(valid, &and(bound, &old_support), &row_proof);
    let rest_proof = right(valid, &and(bound, &old_support), &row_proof);
    let bound_proof = left(bound, &old_support, &rest_proof);
    let after_bound_proof = if pop {
        bound_proof
    } else {
        format!("(ir_byte_world_lt_raise_v1 (ir_byte_alloc_owner_v1 a) next {bound_proof})")
    };
    let support_proof = format!(
        "(ir_byte_world_support_{}_v1 {live} {global} {same} {member} {})",
        if pop { "pop" } else { "push" },
        right(bound, &old_support, &rest_proof)
    );
    let new_row = and(valid, &and(&raised_bound, &new_support));
    let proof = join(
        &new("tail"),
        &new_row,
        &format!("(ih {})", left(&old("tail"), &old_row, "h")),
        &join(
            valid,
            &and(&raised_bound, &new_support),
            &valid_proof,
            &join(
                &raised_bound,
                &new_support,
                &after_bound_proof,
                &support_proof,
            ),
        ),
    );
    let after_mem = if pop {
        "(ir_byte_retire_v1 owner mem)"
    } else {
        "mem"
    };
    (
        name,
        format!(
            "def {name} (mem : IRByteMemoryV1) {}(owners : IRList Nat) (next : Nat)\n\
      (h : @Eq Bool (ir_byte_memory_owners_v1 mem {before_owners} next) Bool.true) :\n\
      @Eq Bool (ir_byte_memory_owners_v1 {after_mem} {after_owners} {after_next}) Bool.true :=\n\
      @IRList.rec IRByteAllocationV1\n\
        (fun (xs : IRList IRByteAllocationV1) => @Eq Bool {} Bool.true -> @Eq Bool {} Bool.true)\n\
        (fun (_ : @Eq Bool Bool.true Bool.true) => @Eq.refl Bool Bool.true)\n\
        (fun (a : IRByteAllocationV1) (tail : IRList IRByteAllocationV1)\n\
          (ih : @Eq Bool {} Bool.true -> @Eq Bool {} Bool.true) =>\n\
          fun (h : @Eq Bool {} Bool.true) => {proof}) (ir_byte_mem_allocs_v1 mem) h",
            if pop { "(owner : Nat) " } else { "" },
            old("xs"),
            new("xs"),
            old("tail"),
            new("tail"),
            old("(@IRList.cons IRByteAllocationV1 a tail)")
        ),
    )
}

fn world_law(pop: bool) -> (&'static str, String) {
    let name = if pop {
        "ir_byte_world_pop_shape_v1"
    } else {
        "ir_byte_world_push_shape_v1"
    };
    let tail = "(ir_byte_length_v1 IRFrame tail)";
    let old_owners = if pop {
        "(@IRList.cons Nat owner owners)"
    } else {
        "owners"
    };
    let old_frames = if pop {
        "(@IRList.cons IRFrame returning (@IRList.cons IRFrame caller tail))"
    } else {
        "(@IRList.cons IRFrame caller tail)"
    };
    let new_frames = if pop {
        "(@IRList.cons IRFrame updated tail)"
    } else {
        "(@IRList.cons IRFrame inserted (@IRList.cons IRFrame updated tail))"
    };
    let old_world = format!("(@IRByteWorldV1.mk W mem host {old_owners} next)");
    let new_world = format!(
        "(ir_byte_{}_owner_v1 W {old_world})",
        if pop { "pop" } else { "push" }
    );
    let empty = "(ir_nat_eqb (ir_byte_length_v1 IRMemSlot legacy) 0)";
    let old_count = format!("(ir_nat_eqb (ir_byte_length_v1 IRFrame {old_frames}) (ir_byte_length_v1 Nat {old_owners}))");
    let valid_owners = format!("(ir_byte_owners_valid_v1 {old_owners} next)");
    let valid_memory = format!("(ir_byte_memory_owners_v1 mem {old_owners} next)");
    let conjunction = and(&old_count, &and(&valid_owners, &valid_memory));
    let empty_proof = left(empty, &conjunction, "before");
    let remainder = right(empty, &conjunction, "before");
    let count_proof = left(&old_count, &and(&valid_owners, &valid_memory), &remainder);
    let both = right(&old_count, &and(&valid_owners, &valid_memory), &remainder);
    let owners_proof = left(&valid_owners, &valid_memory, &both);
    let memory_proof = right(&valid_owners, &valid_memory, &both);
    let smaller_count = format!("(ir_nat_eqb (Nat.succ {tail}) (ir_byte_length_v1 Nat owners))");
    let larger_count = format!(
        "(ir_nat_eqb (Nat.succ (Nat.succ {tail})) (Nat.succ (ir_byte_length_v1 Nat owners)))"
    );
    let eq_succ =
        format!("(ir_byte_world_eq_succ_v1 (Nat.succ {tail}) (ir_byte_length_v1 Nat owners))");
    let new_count = if pop {
        smaller_count.clone()
    } else {
        larger_count.clone()
    };
    let new_count_proof = if pop {
        format!("(@Eq.trans Bool {smaller_count} {larger_count} Bool.true (@Eq.symm Bool {larger_count} {smaller_count} {eq_succ}) {count_proof})")
    } else {
        format!("(@Eq.trans Bool {larger_count} {smaller_count} Bool.true {eq_succ} {count_proof})")
    };
    let (new_owners, new_memory, owners_proof, memory_proof) = if pop {
        (
            "(ir_byte_owners_valid_v1 owners next)".to_owned(),
            "(ir_byte_memory_owners_v1 (ir_byte_retire_v1 owner mem) owners next)".to_owned(),
            format!("(ir_byte_owners_tail_v1 owner owners next {owners_proof})"),
            format!("(ir_byte_memory_owners_pop_v1 mem owner owners next {memory_proof})"),
        )
    } else {
        (
            "(ir_byte_owners_valid_v1 (@IRList.cons Nat next owners) (Nat.succ next))".to_owned(),
            "(ir_byte_memory_owners_v1 mem (@IRList.cons Nat next owners) (Nat.succ next))"
                .to_owned(),
            format!("(ir_byte_owners_push_v1 owners next {owners_proof})"),
            format!("(ir_byte_memory_owners_push_v1 mem owners next {memory_proof})"),
        )
    };
    let proof = join(
        empty,
        &and(&new_count, &and(&new_owners, &new_memory)),
        &empty_proof,
        &join(
            &new_count,
            &and(&new_owners, &new_memory),
            &new_count_proof,
            &join(&new_owners, &new_memory, &owners_proof, &memory_proof),
        ),
    );
    (name, format!("def {name} (W : Type) (mem : IRByteMemoryV1) (host : W) {}\n\
      (owners : IRList Nat) (next : Nat) (caller : IRFrame) (updated : IRFrame)\n\
      (tail : IRList IRFrame) (legacy : IRList IRMemSlot) (cursor : Nat)\n\
      (before : @Eq Bool (ir_byte_world_valid_v1 W (IRMachine.mk {old_frames} legacy cursor) {old_world}) Bool.true) :\n\
      @Eq Bool (ir_byte_world_valid_v1 W (IRMachine.mk {new_frames} legacy cursor) {new_world}) Bool.true :=\n\
      {proof}", if pop { "(owner : Nat) (returning : IRFrame)" } else { "(inserted : IRFrame)" }))
}

fn laws() -> Result<Vec<(&'static str, String)>, SpecError> {
    let mut out = vec![
        ("ir_byte_world_false_true_v1", BOOL_FALSE_TRUE.into()),
        ("ir_byte_world_and_left_v1", AND_LEFT.into()),
        ("ir_byte_world_and_right_v1", AND_RIGHT.into()),
        ("ir_byte_world_and_intro_v1", AND_INTRO.into()),
        ("ir_byte_world_or_false_v1", OR_FALSE.into()),
        ("ir_byte_world_lt_raise_walk_v1", LT_RAISE_WALK.into()),
        ("ir_byte_world_lt_raise_v1", LT_RAISE.into()),
        ("ir_byte_world_lt_ne_walk_v1", LT_NE_WALK.into()),
        ("ir_byte_world_lt_ne_v1", LT_NE.into()),
        ("ir_byte_world_eq_succ_v1", EQ_SUCC.into()),
    ];
    out.extend(support_laws()?);
    out.extend(owners_laws());
    out.push(memory_law(false));
    out.push(memory_law(true));
    out.push(world_law(false));
    out.push(world_law(true));
    Ok(out)
}

impl Specification {
    /// Install checked pre-state-to-post-state activation-world preservation.
    pub(super) fn add_eval_ir_byte_world_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in laws()? {
            self.add_recursive_def(&source, "Checked actual activation-world preservation; no postcondition or provider-fidelity premise.")
                .map_err(|error| match error {
                    SpecError::ParseError(detail) => SpecError::ParseError(format!("{name}: {detail}")),
                    SpecError::ElabError(detail) => SpecError::ElabError(format!("{name}: {detail}")),
                    SpecError::TypeError(detail) => SpecError::TypeError(format!("{name}: {detail}")),
                    other => other,
                })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

    fn spec() -> Specification {
        Specification::new_eval_ir_byte_prelude_spec_v1().expect("actual byte profile")
    }

    fn checked(spec: &Specification, name: &str) {
        let definition = spec
            .get_definition(name)
            .expect("installed checked declaration");
        assert!(!definition.is_axiom);
        assert!(definition.elaborated_value.is_some());
        spec.verify_definition(name)
            .expect("independent kernel replay");
        let name = Name::from_string(name);
        assert!(spec
            .env()
            .axiom_deps(&name)
            .expect("existing root")
            .is_empty());
        assert!(spec
            .env()
            .trust_marker_deps(&name)
            .expect("existing root")
            .is_empty());
    }

    #[test]
    fn world_laws_are_checked_without_axioms_or_trust_markers() {
        crate::test_utils::run_with_stack(|| {
            let spec = spec();
            for (name, _) in laws().expect("valid proof candidates") {
                checked(&spec, name);
            }
        });
    }

    #[test]
    fn actual_push_and_return_preserve_their_running_worlds() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            spec.add_recursive_def(
                r"def world_actual_push_consumer
  (W : Type) (mem : IRByteMemoryV1) (host : W) (owners : IRList Nat) (next : Nat)
  (caller : IRFrame) (tail : IRList IRFrame) (legacy : IRList IRMemSlot) (cursor : Nat)
  (destinations : IRList Nat) (callee : IRFunc) (values : IRList IRScalar)
  (before : @Eq Bool (ir_byte_world_valid_v1 W
    (IRMachine.mk (@IRList.cons IRFrame caller tail) legacy cursor)
    (@IRByteWorldV1.mk W mem host owners next)) Bool.true) :
@IRConfig.rec (fun (_ : IRConfig) => Prop)
  (fun (machine : IRMachine) => @Eq Bool (ir_byte_world_valid_v1 W machine
    (ir_byte_push_owner_v1 W (@IRByteWorldV1.mk W mem host owners next))) Bool.true)
  (fun (_ : IROutcome) => False)
  (ir_push (IRMachine.mk (@IRList.cons IRFrame caller tail) legacy cursor) destinations callee values) :=
ir_byte_world_push_shape_v1 W mem host
  (IRFrame.mk (ir_func_id callee) (ir_func_entry callee) 0
    (ir_bind_params (ir_func_params callee) values (@IRList.nil IRBinding)) destinations)
  owners next caller (ir_frame_advance caller) tail legacy cursor before",
                "Actual shared ir_push result, not a replacement frame evaluator",
            ).expect("universal actual push consumer");
            checked(&spec, "world_actual_push_consumer");
            spec.add_recursive_def(
                r"def world_actual_return_consumer
  (W : Type) (mem : IRByteMemoryV1) (host : W) (owner : Nat)
  (owners : IRList Nat) (next : Nat) (returning : IRFrame) (caller : IRFrame)
  (tail : IRList IRFrame) (legacy : IRList IRMemSlot) (cursor : Nat) (values : IRList IRScalar)
  (before : @Eq Bool (ir_byte_world_valid_v1 W
    (IRMachine.mk (@IRList.cons IRFrame returning (@IRList.cons IRFrame caller tail)) legacy cursor)
    (@IRByteWorldV1.mk W mem host (@IRList.cons Nat owner owners) next)) Bool.true) :
@IRConfig.rec (fun (_ : IRConfig) => Prop)
  (fun (machine : IRMachine) => @Eq Bool (ir_byte_world_valid_v1 W machine
    (ir_byte_pop_owner_v1 W (@IRByteWorldV1.mk W mem host (@IRList.cons Nat owner owners) next))) Bool.true)
  (fun (_ : IROutcome) => False)
  (ir_ret_vals (IRMachine.mk (@IRList.cons IRFrame returning (@IRList.cons IRFrame caller tail)) legacy cursor) values) :=
ir_byte_world_pop_shape_v1 W mem host owner returning owners next caller
  (ir_frame_set_many caller (ir_frame_dests returning) values) tail legacy cursor before",
                "Actual shared ir_ret_vals result with the exact retired activation world",
            ).expect("universal actual return consumer");
            checked(&spec, "world_actual_return_consumer");
        });
    }

    fn allocation(base: u64, owner: u64, live: bool) -> String {
        format!("(IRByteAllocationV1.mk {base} 8 {owner} Bool.{live})")
    }

    fn allocations(rows: &[(u64, u64, bool)]) -> String {
        rows.iter().rev().fold(
            "(@IRList.nil IRByteAllocationV1)".into(),
            |tail, &(base, owner, live)| {
                format!(
                    "(@IRList.cons IRByteAllocationV1 {} {tail})",
                    allocation(base, owner, live)
                )
            },
        )
    }

    const FRAME: &str = "(IRFrame.mk 1 0 0 (@IRList.nil IRBinding) (@IRList.nil Nat))";
    const CALLER: &str = "(IRFrame.mk 0 0 7 (@IRList.nil IRBinding) (@IRList.nil Nat))";
    const OWNERS: &str = "(@IRList.cons Nat 1 (@IRList.nil Nat))";
    const NO_FRAMES: &str = "(@IRList.nil IRFrame)";
    const NO_LEGACY: &str = "(@IRList.nil IRMemSlot)";

    #[test]
    fn inhabited_world_preserves_global_caller_callee_and_old_dead_allocations() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            // An arbitrary byte map and host value survive. There is a live
            // callee row, a live caller row after it, a global row, and an old
            // inactive owner. This is not a singleton-allocation shortcut.
            let rows = allocations(&[(32, 2, true), (16, 1, true), (48, 0, true), (64, 3, false)]);
            let memory = format!("(IRByteMemoryV1.mk {rows} bytes 80)");
            let world =
                format!("(@IRByteWorldV1.mk Nat {memory} host (@IRList.cons Nat 2 {OWNERS}) 4)");
            let source = format!("def world_pop_inhabited (bytes : Nat -> IROption Nat) (host : Nat) :\n\
              @Eq Bool (ir_byte_world_valid_v1 Nat (IRMachine.mk (@IRList.cons IRFrame {CALLER} {NO_FRAMES}) {NO_LEGACY} 1)\n\
                (ir_byte_pop_owner_v1 Nat {world})) Bool.true :=\n\
              ir_byte_world_pop_shape_v1 Nat {memory} host 2 {FRAME} {OWNERS} 4 {CALLER} {CALLER}\n\
                {NO_FRAMES} {NO_LEGACY} 1 (@Eq.refl Bool Bool.true)");
            spec.add_recursive_def(
                &source,
                "Inhabited quantified host/byte world through generic pop preservation",
            )
            .expect("inhabited pop world");
            checked(&spec, "world_pop_inhabited");
            let source = format!("def world_push_inhabited (bytes : Nat -> IROption Nat) (host : Nat) :\n\
              @Eq Bool (ir_byte_world_valid_v1 Nat\n\
                (IRMachine.mk (@IRList.cons IRFrame {FRAME} (@IRList.cons IRFrame {FRAME} (@IRList.cons IRFrame {CALLER} {NO_FRAMES}))) {NO_LEGACY} 1)\n\
                (ir_byte_push_owner_v1 Nat {world})) Bool.true :=\n\
              ir_byte_world_push_shape_v1 Nat {memory} host {FRAME} (@IRList.cons Nat 2 {OWNERS}) 4 {FRAME} {FRAME}\n\
                (@IRList.cons IRFrame {CALLER} {NO_FRAMES}) {NO_LEGACY} 1 (@Eq.refl Bool Bool.true)");
            spec.add_recursive_def(
                &source,
                "Fresh owner four with existing live/global/dead allocations",
            )
            .expect("inhabited push world");
            checked(&spec, "world_push_inhabited");
        });
    }

    fn reject(spec: &mut Specification, name: &str, source: &str) {
        let error = spec
            .add_recursive_def(source, "Invalid world-preservation claim")
            .expect_err("malformed pre-state or post-state must fail");
        crate::test_utils::assert_type_mismatch_rejection(&error, name);
        assert!(spec.get_definition(name).is_none());
    }

    #[test]
    fn world_laws_reject_stale_owners_live_orphans_and_missing_frames() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            for (name, owners, next) in [
                (
                    "world_bad_duplicate",
                    "(@IRList.cons Nat 1 (@IRList.cons Nat 1 (@IRList.nil Nat)))",
                    2,
                ),
                (
                    "world_bad_zero_owner",
                    "(@IRList.cons Nat 0 (@IRList.nil Nat))",
                    2,
                ),
                (
                    "world_bad_stale_next",
                    "(@IRList.cons Nat 2 (@IRList.nil Nat))",
                    2,
                ),
            ] {
                reject(&mut spec, name, &format!("def {name} : @Eq Bool (ir_byte_owners_valid_v1 (@IRList.cons Nat {next} {owners}) (Nat.succ {next})) Bool.true := ir_byte_owners_push_v1 {owners} {next} (@Eq.refl Bool Bool.true)"));
            }
            let orphan = format!(
                "(IRByteMemoryV1.mk {} (fun (_ : Nat) => @IROption.none Nat) 80)",
                allocations(&[(16, 3, true)])
            );
            reject(&mut spec, "world_bad_live_orphan", &format!("def world_bad_live_orphan : @Eq Bool (ir_byte_memory_owners_v1 (ir_byte_retire_v1 2 {orphan}) {OWNERS} 4) Bool.true := ir_byte_memory_owners_pop_v1 {orphan} 2 {OWNERS} 4 (@Eq.refl Bool Bool.true)"));
            let empty_memory = "(ir_byte_memory_empty_v1 16)";
            let world = format!("(@IRByteWorldV1.mk Nat {empty_memory} 0 {OWNERS} 2)");
            let missing_frame = format!("def world_bad_missing_frame : @Eq Bool (ir_byte_world_valid_v1 Nat\n\
              (IRMachine.mk (@IRList.cons IRFrame {CALLER} {NO_FRAMES}) {NO_LEGACY} 1)\n\
              (ir_byte_push_owner_v1 Nat {world})) Bool.true :=\n\
              ir_byte_world_push_shape_v1 Nat {empty_memory} 0 {FRAME} {OWNERS} 2 {CALLER} {CALLER}\n\
                {NO_FRAMES} {NO_LEGACY} 1 (@Eq.refl Bool Bool.true)");
            reject(&mut spec, "world_bad_missing_frame", &missing_frame);
        });
    }
}

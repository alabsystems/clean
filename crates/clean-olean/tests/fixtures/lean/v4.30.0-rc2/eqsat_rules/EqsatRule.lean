/- EqsatRule: what a trust-cg e-graph rewrite rule says, over SemR (PKG-U2).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   A rule of trust-cg's rule files (trust-cg `docs/eqsat-tier-e.md` section 5.1)
   is quoted as a closed `Rule` literal, and `Sound rule T` is the one statement
   a discharge record proves about it at an instance type `T`. trust-cg builds
   the literal from its checker's parsed rule and asks the kernel to accept a
   lemma of this family for `Sound <literal> <type>`; nothing else is stated in
   Rust, so these definitions are the meaning of a rule and are trusted as
   read. `EqsatAnchors.lean` pins what they mean with kernel-checked
   statements (the gate requires each by name and pins its statement), and
   `EqsatIntControls.lean` refutes wrong rules through them.

   Rules of this file:
   * it imports SemR only and every operator is evaluated by SemR's own
     evaluator (`evalBinop`, `evalUnop`, `evalIcmp`, `selectVal`); no operator
     arithmetic is written here;
   * every inductive is flat (no nested or mutual inductive, no `List` of
     patterns), every definition is by structural recursion or a plain match,
     and nothing is universe polymorphic, so a `Rule` literal is a closed,
     binder-free, level-free term;
   * no string literal: a pattern that is not a term of the instance type
     (an unbound variable, `(const INT)` at `bool`) evaluates to
     `.stop .outOfFuel`, which is neither a value nor undefined behaviour. An
     `equiv` statement with such a pattern on either side, and a `refines`
     statement with it on the left side, fails on every assignment that
     satisfies the hypotheses (`EqsatAnchors.equiv_stop_never`,
     `refines_stop_left`). It is not true that no `Sound` statement about a
     non-term holds: a `refines` statement constrains its right side only on
     assignments where the left side is a value
     (`EqsatAnchors.refines_value_left`), so one whose left side is always
     undefined behaviour holds with any right side
     (`EqsatIntControls.refines_ub_left_any_rhs`); and a statement whose side
     conditions no assignment satisfies holds whatever its sides are
     (`Satisfiable` below). The first needs an operator that is not total;
     the rule grammar admits none, and for a left side of total operators the
     `refines` statement is the `equiv` statement
     (`EqsatAnchors.refines_gives_equiv_of_total`).

   How this mirrors the checker's replay (trust-cg
   `crates/trust-cg-eqsat-check/src/replay.rs`, `rule_step` and `instantiate`):
   * a variable is bound to a defined term of type `sort.at(T)`; its value is a
     residue below the type's modulus, or a `Bool` (`Admits`). A constant
     variable is bound to a constant term, which ranges over the same values,
     so `Admits` reads the `const` flag of `Sorts.cons` as data only: it is
     part of the literal and of the literal's digest, and it does not reach
     the proposition. The kernel binds a lemma to the proposition
     `Sound <literal> <type>`, not to the literal: two literals that differ
     only in a `const` flag, in `var` against `cvar`, or in two integer
     literals of one residue at the instance type state the same thing
     (`EqsatAnchors.const_flag_is_data`, `var_cvar_one_statement`,
     `EqsatIntControls.same_residue_one_statement`), and Clean's entry
     accepts a lemma of one for the other (the gate asserts two such
     acceptances). Telling such literals apart is the rule digest's work, in
     trust-cg;
   * `(const INT)` is `Const(T, INT mod 2^w)` (`Int::residue`): `litR`;
   * `OP` at instance type `T` is the term operator `ROp::at(T)`: operand type
     `Bool` for `band bor bxor`, else `T` (`binTy`);
   * `(eval OP ?a ...)` is quoted as `OP` over the constant variables
     (`Pat.cvar`), so the checker's ground evaluator (`semantics.rs`) stays a
     named premise (`checker-ground-eval`) of every rule that uses `eval`.
     The statement of an `eval` rule and of its `eval`-free twin are the same
     term, so whether a rule uses `eval` is read from the parsed rule, never
     from the statement;
   * a side condition tests the residue of a constant variable exactly as
     `rule_step` does (`Cond.holds`).
-/
import SemR

namespace EqsatRule
open SemR

/-- A sort of the rule grammar: the instance type `T`, or `bool`. -/
inductive Srt where
  | t
  | bool

/-- The rule's variables in the order of their names' bytes (the checker's
    `BTreeMap<String, VarInfo>`, the order a derivation's substitution uses):
    each one's sort and whether it is a constant variable. -/
inductive Sorts where
  | nil
  | cons (s : Srt) (const : Bool) (rest : Sorts)

/-- A pattern (section 5.1 `PAT`). `var i` and `cvar i` are `?v` and
    `(const ?v)` for the variable of rank `i`; `lit neg mag` is `(const INT)`
    with `INT = -mag` when `neg`, else `mag`; `(eval OP ?a ...)` is `OP` over
    `cvar`s. -/
inductive Pat where
  | var (i : Nat)
  | cvar (i : Nat)
  | lit (neg : Bool) (mag : Nat)
  | tt
  | ff
  | bin (op : BinOp) (a b : Pat)
  | un (op : UnOp) (a : Pat)
  | cmp (op : ICmpOp) (a b : Pat)
  | sel (c a b : Pat)

/-- A side condition (section 5.1 `COND`) on the variable of rank `i`. -/
inductive Cond where
  | eq (i : Nat) (neg : Bool) (mag : Nat)
  | ne (i : Nat) (neg : Bool) (mag : Nat)
  | pow2 (i : Nat)
  | zeroModWidth (i : Nat)

inductive Conds where
  | nil
  | cons (c : Cond) (rest : Conds)

inductive Dir where
  | equiv
  | refines

/-- One rule statement: direction, variables, both sides, side conditions.
    The domain is not part of it: `Sound` is stated per instance type. -/
structure Rule where
  dir : Dir
  vars : Sorts
  lhs : Pat
  rhs : Pat
  conds : Conds

/-- An instance type: one of SemR's integer types, or `Bool`. -/
inductive STy where
  | int (t : IntTy)
  | bool

/-- The SemR type an instance type is. -/
def STy.ty : STy → Ty
  | .int t => .int t
  | .bool => .bool

/-- The SemR type of a sort at instance type `T` (the checker's `Sort::at`). -/
def Srt.ty (T : STy) : Srt → Ty
  | .t => T.ty
  | .bool => .bool

/-- The operand type of a binary `OP` at instance type `T` (the checker's
    `ROp::at`): `Bool` for `band bor bxor`, else `T`. -/
def binTy (T : STy) : BinOp → Ty
  | .bAnd => .bool
  | .bOr => .bool
  | .bXor => .bool
  | _ => T.ty

/-- `INT mod 2^w` for `INT = -mag` when `neg`, else `mag` (the checker's
    `Int::residue`), spelled with SemR's `negR` and `modulus`. -/
def litR (w : Nat) (neg : Bool) (mag : Nat) : Nat :=
  match neg with
  | true => negR w mag
  | false => mag % modulus w

/-- `(const INT)` at instance type `T`: `Const(T, INT mod 2^w)`, and not a
    term at `Bool` (the checker's `instantiate` refuses it there). -/
def litVal (pb : Nat) (T : STy) (neg : Bool) (mag : Nat) : R Val :=
  match T with
  | .int t => .ok (.int t (litR (t.bits pb) neg mag))
  | .bool => .stop .outOfFuel

/-- The value bound to the variable of rank `i`; an unbound rank is not a
    term. -/
def getVar : List Val → Nat → R Val
  | [], _ => .stop .outOfFuel
  | v :: _, 0 => .ok v
  | _ :: vs, i + 1 => getVar vs i

/-- The value of a pattern at instance type `T` under an assignment, by
    SemR's own evaluators. `pb` is the module's pointer width in bits. -/
def Pat.eval (pb : Nat) (T : STy) (env : List Val) : Pat → R Val
  | .var i => getVar env i
  | .cvar i => getVar env i
  | .lit neg mag => litVal pb T neg mag
  | .tt => .ok (.bool true)
  | .ff => .ok (.bool false)
  | .bin op a b =>
    (a.eval pb T env).bind fun x =>
    (b.eval pb T env).bind fun y =>
    evalBinop pb op (binTy T op) x y
  | .un op a =>
    (a.eval pb T env).bind fun x =>
    evalUnop pb op T.ty x
  | .cmp op a b =>
    (a.eval pb T env).bind fun x =>
    (b.eval pb T env).bind fun y =>
    evalIcmp pb op T.ty x y
  | .sel c a b =>
    (c.eval pb T env).bind fun cv =>
    (a.eval pb T env).bind fun x =>
    (b.eval pb T env).bind fun y =>
    selectVal pb T.ty cv x y

/-- A value a variable of sort `s` can be bound to at instance type `T`: a
    residue below the type's modulus, or a `Bool`. Never poison: a graph
    variable ranges over defined values only (section 2.3). -/
def AdmitsVal (pb : Nat) (T : STy) (s : Srt) (v : Val) : Prop :=
  match s, T with
  | .t, .int t => ∃ r, v = .int t r ∧ r < modulus (t.bits pb)
  | .t, .bool => ∃ b, v = .bool b
  | .bool, _ => ∃ b, v = .bool b

/-- An assignment the rule's variables admit: exactly one admitted value per
    variable, in rank order. -/
def Admits (pb : Nat) (T : STy) : Sorts → List Val → Prop
  | .nil, [] => True
  | .cons s _ rest, v :: vs => AdmitsVal pb T s v ∧ Admits pb T rest vs
  | _, _ => False

/-- `P w r` for the width `w` of the instance type and the residue `r` of the
    variable of rank `i`. Where the variable has no residue (the instance type
    is `Bool`, or the rank is unbound or bound to a non-integer) the condition
    says nothing and holds: the checker never accepts a side condition there,
    and a statement must not become easier because its condition is
    malformed. -/
def onResidue (pb : Nat) (T : STy) (env : List Val) (i : Nat) (P : Nat → Nat → Prop) : Prop :=
  match T, getVar env i with
  | .int t, .ok (.int _ r) => P (t.bits pb) r
  | _, _ => True

/-- One side condition, as the checker's `rule_step` tests it on the residue
    of a constant variable: `eq`/`ne` against `INT mod 2^w`, `pow2` exactly one
    bit set, `zeroModWidth` a multiple of the width. -/
def Cond.holds (pb : Nat) (T : STy) (env : List Val) : Cond → Prop
  | .eq i neg mag => onResidue pb T env i fun w r => r = litR w neg mag
  | .ne i neg mag => onResidue pb T env i fun w r => r ≠ litR w neg mag
  | .pow2 i => onResidue pb T env i fun _ r => ∃ k, r = 2 ^ k
  | .zeroModWidth i => onResidue pb T env i fun w r => r % w = 0

def CondsHold (pb : Nat) (T : STy) (env : List Val) : Conds → Prop
  | .nil => True
  | .cons c rest => c.holds pb T env ∧ CondsHold pb T env rest

/-- The pointer widths a statement at `T` covers (the checker's `Ctx::width`):
    32 or 64 at `isize` and `usize`, every width at any other type. -/
def PbOk : STy → Nat → Prop
  | .int .isize, pb => pb = 32 ∨ pb = 64
  | .int .usize, pb => pb = 32 ∨ pb = 64
  | _, _ => True

/-- What a direction says of the two sides' outcomes. `equiv`: one common
    value (so both sides are defined). `refines`: the left side is undefined
    behaviour, or one common value. -/
def Holds : Dir → R Val → R Val → Prop
  | .equiv, l, r => ∃ v, l = .ok v ∧ r = .ok v
  | .refines, l, r => (∃ m, l = .stop (.ub m)) ∨ (∃ v, l = .ok v ∧ r = .ok v)

/-- The statement of a rule at an instance type: under every admitted pointer
    width and assignment that satisfies the side conditions, the two sides
    stand as the direction says. -/
def Sound (r : Rule) (T : STy) : Prop :=
  ∀ pb env, PbOk T pb → Admits pb T r.vars env → CondsHold pb T env r.conds →
    Holds r.dir (r.lhs.eval pb T env) (r.rhs.eval pb T env)

/-- The side conditions of a rule can be met at `T`: at every admitted pointer
    width some admitted assignment satisfies them. `Sound` does not say this:
    a rule whose conditions contradict each other at `T` is `Sound` there
    whatever its sides are (it never fires in the checker, which tests the
    same conditions). A rule with a `where` clause is to carry a lemma of
    this statement beside its `Sound` lemma at each integer type; a rule with
    none, and any rule at `Bool`, has it for nothing
    (`EqsatAnchors.satisfiable_of_no_conds`, `satisfiable_bool`). -/
def Satisfiable (r : Rule) (T : STy) : Prop :=
  ∀ pb, PbOk T pb → ∃ env, Admits pb T r.vars env ∧ CondsHold pb T env r.conds

end EqsatRule

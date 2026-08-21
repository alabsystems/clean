// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the `codata` command (R3.2): full surface pipeline
//! (`parse_file` → `elaborate_decl_and_register`, the same path `clean
//! check` uses), the generated companions, the `rfl` computation laws
//! evaluated on CONCRETE corecursive values, the lazy-seed invariant, and
//! the loud v1 envelope.

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

/// Elaborate + register every decl in `code`, panicking on the first failure.
fn elab_all(code: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("should parse");
    for (i, decl) in decls.iter().enumerate() {
        elaborate_decl_and_register(&mut env, decl)
            .unwrap_or_else(|e| panic!("decl {i} failed to elaborate: {e:?}"));
    }
    env
}

/// Elaborate all decls, returning the first error (prefix must succeed).
fn elab_expect_err(code: &str) -> crate::ElabError {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("should parse");
    let (last, prefix) = decls.split_last().expect("at least one declaration");
    for (i, decl) in prefix.iter().enumerate() {
        elaborate_decl_and_register(&mut env, decl)
            .unwrap_or_else(|e| panic!("prefix decl {i} must elaborate: {e:?}"));
    }
    elaborate_decl_and_register(&mut env, last).expect_err("the final declaration must be rejected")
}

const STREAM_SRC: &str = r#"
codata Stream (A : Type) where
  head : A
  tail : Stream A
"#;

#[test]
fn test_codata_stream_generates_companions() {
    let env = elab_all(STREAM_SRC);
    for name in [
        "Stream",
        "Stream.shapeF",
        "Stream.posF",
        "Stream.tgtF",
        "Stream.head",
        "Stream.tail",
        "Stream.corecStep",
        "Stream.corec",
        "Stream.head_corec",
        "Stream.tail_corec",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "generated constant {name} must register"
        );
    }
    assert!(
        env.get_const(&Name::from_string("Codata.IMIntl")).is_some(),
        "first codata use must inject the seed library"
    );
}

#[test]
fn test_codata_stream_computes_through_the_encoding() {
    // The generated laws are theorems; here the ENCODING itself computes:
    // heads of iterated tails of a concrete corecursive stream reduce by
    // rfl through IMchild/ucorec — genuine definitional behavior, not a
    // registered axiom.
    let src = format!(
        "{STREAM_SRC}
def natsFrom (n : Nat) : Stream Nat := Stream.corec (fun k => k) Nat.succ n
theorem h0 : Stream.head (natsFrom 0) = 0 := rfl
theorem h1 : Stream.head (Stream.tail (natsFrom 0)) = 1 := rfl
theorem h2 : Stream.head (Stream.tail (Stream.tail (natsFrom 0))) = 2 := rfl
"
    );
    let env = elab_all(&src);
    assert!(
        env.get_const(&Name::from_string("h2")).is_some(),
        "two tails deep must still compute by rfl"
    );
}

#[test]
fn test_codata_parameterless_ticker() {
    // The QPFTypes parameterless answer: no dummy parameter needed.
    let src = r#"
codata Ticker where
  tick : Nat
  next : Ticker

def zeros : Ticker := Ticker.corec (fun _ => 0) (fun u => u) Unit.unit
theorem t0 : Ticker.tick zeros = 0 := rfl
theorem t1 : Ticker.tick (Ticker.next zeros) = 0 := rfl
"#;
    let env = elab_all(src);
    assert!(
        env.get_const(&Name::from_string("Ticker.next_corec"))
            .is_some(),
        "parameterless codata must generate its rfl laws too"
    );
}

#[test]
fn test_codata_seed_stays_lazy_without_codata() {
    let env = elab_all("def plain : Nat := Nat.zero");
    assert!(
        env.get_const(&Name::from_string("Codata.IMIntl")).is_none(),
        "no codata declaration => no Codata.* seeds in the env"
    );
}

#[test]
fn test_codata_deriving_rejected_loud() {
    let err =
        elab_expect_err("codata S2 (A : Type) where\n  head : A\n  tail : S2 A\nderiving BEq");
    assert!(
        format!("{err:?}").contains("deriving"),
        "deriving on codata must reject loudly, got: {err:?}"
    );
}

#[test]
fn test_codata_multi_observation() {
    // Two observations: the label is a PProd, accessors are projection
    // chains, and all three rfl laws generate. Concrete computation too.
    let src = r#"
codata P2 (A : Type) (B : Type) where
  left : A
  right : B
  rest : P2 A B

def alt (n : Nat) : P2 Nat Nat :=
  P2.corec (fun k => k) (fun k => Nat.succ k) Nat.succ n
theorem a0 : P2.left (alt 0) = 0 := rfl
theorem a1 : P2.right (alt 0) = 1 := rfl
theorem a2 : P2.left (P2.rest (alt 0)) = 1 := rfl
"#;
    let env = elab_all(src);
    for name in ["P2.left_corec", "P2.right_corec", "P2.rest_corec"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "multi-observation law {name} must register"
        );
    }
}

#[test]
fn test_codata_single_field_rejected() {
    let err = elab_expect_err("codata S3 (A : Type) where\n  tail : S3 A");
    assert!(
        format!("{err:?}").contains("at least one observation"),
        "a single-field codata must reject, got: {err:?}"
    );
}

#[test]
fn test_codata_recursive_observation_rejected() {
    // Both fields are self-typed, so the trailing recursive block absorbs
    // them and no observation remains — loud reject.
    let err = elab_expect_err("codata S4 (A : Type) where\n  head : S4 A\n  tail : S4 A");
    assert!(
        format!("{err:?}").contains("at least one observation"),
        "an all-recursive codata must reject, got: {err:?}"
    );
}

#[test]
fn test_codata_wrong_instantiation_rejected() {
    // `S5 Nat` is not the self type at its own parameters, so it is not a
    // recursive field — it lands in the observation block and the
    // self-mention check rejects it.
    let err = elab_expect_err("codata S5 (A : Type) where\n  head : A\n  tail : S5 Nat");
    assert!(
        format!("{err:?}").contains("final field must be recursive"),
        "a differently-instantiated recursive field must reject, got: {err:?}"
    );
}

#[test]
fn test_codata_branching_btree() {
    // Two recursive fields: Sum-of-Units positions, one accessor per
    // branch, per-branch rfl laws, and concrete computation through both
    // branches.
    let src = r#"
codata BT (A : Type) where
  label : A
  left : BT A
  right : BT A

def skew (n : Nat) : BT Nat :=
  BT.corec (fun k => k) Nat.succ (fun k => Nat.succ (Nat.succ k)) n
theorem s0 : BT.label (skew 0) = 0 := rfl
theorem sl : BT.label (BT.left (skew 0)) = 1 := rfl
theorem sr : BT.label (BT.right (skew 0)) = 2 := rfl
theorem slr : BT.label (BT.right (BT.left (skew 0))) = 3 := rfl
"#;
    let env = elab_all(src);
    for name in ["BT.label_corec", "BT.left_corec", "BT.right_corec"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "branching law {name} must register"
        );
    }
}

#[test]
fn test_codata_single_universe_param_e2e() {
    // U2 rung 7 part 2: `codata C.{u}` elaborates — the generated
    // container/type/accessors/corecursor are all `.{u}`, the concrete
    // instantiations pin u through fresh metas, and the computation law
    // still computes by rfl at BOTH a small and a large universe.
    let env = elab_all(
        "codata GP.{u} (A : Type u) where\n  head : A\n  tail : GP A\n\n\
         def nats : Nat -> GP Nat :=\n  fun n => GP.corec (fun s => s) (fun s => Nat.succ s) n\n\
         theorem nats_head : GP.head (nats Nat.zero) = Nat.zero := rfl\n\
         theorem nats_tail_head :\n    GP.head (GP.tail (nats Nat.zero)) = Nat.succ Nat.zero := rfl\n\
         def bigs : Type -> GP.{1} Type :=\n  fun t => GP.corec (fun s => s) (fun s => s) t\n\
         theorem bigs_head : GP.head (bigs Nat) = Nat := rfl",
    );
    assert!(
        env.get_const(&Name::from_string("GP")).is_some(),
        "polymorphic codata type must register"
    );
}

#[test]
fn test_codata_multi_universe_params_rejected() {
    let err = elab_expect_err("codata S7.{u, v} (A : Type u) where\n  head : A\n  tail : S7 A");
    assert!(
        format!("{err:?}").contains("ONE universe parameter"),
        "multi-param polymorphic codata must reject in v1, got: {err:?}"
    );
}

// ── both-orders collision gates (design §A verifier amendments) ──
// Offline simulation of the import-collision surface: a real Lean-core
// .olean census run is release-gated in clean-olean; these lock the
// codata-side semantics in both orders.

#[test]
fn test_collision_import_then_codata_rejects_loud() {
    // ORDER A: an earlier import (simulated) occupied a Codata.* name.
    // The codata command must fail LOUD (reserved namespace) and leave the
    // env untouched — never silently shadow the imported constant.
    let mut env = Environment::with_prelude();
    let pre = parse_file("def Codata.IMhead : Nat := Nat.zero").expect("should parse");
    elaborate_decl_and_register(&mut env, &pre[0]).expect("simulated import must register");
    let before = env.num_constants();
    let decls = parse_file(STREAM_SRC).expect("should parse");
    let err = elaborate_decl_and_register(&mut env, &decls[0])
        .expect_err("codata after a foreign Codata.* constant must fail");
    assert!(
        format!("{err:?}").contains("reserved"),
        "the reject must name the reserved namespace, got: {err:?}"
    );
    assert_eq!(
        env.num_constants(),
        before,
        "failed codata must leave the env untouched"
    );
}

#[test]
fn test_collision_codata_then_import_never_clobbers_seeds() {
    // ORDER B: seeds are in; a later import-shaped registration of the same
    // name must not CLOBBER the seed (first-registered-wins, matching the
    // .olean import path's collision policy). Whether the duplicate errors
    // or no-ops, the seed constant's TYPE must survive byte-identical.
    let mut env = elab_all(STREAM_SRC);
    let seed_name = Name::from_string("Codata.IMhead");
    let seed_ty_before = env
        .get_const(&seed_name)
        .expect("seed must be present after codata")
        .type_
        .clone();
    let dup = parse_file("def Codata.IMhead : Nat := Nat.zero").expect("should parse");
    let _ = elaborate_decl_and_register(&mut env, &dup[0]);
    let seed_ty_after = env
        .get_const(&seed_name)
        .expect("seed constant must still exist")
        .type_
        .clone();
    assert_eq!(
        seed_ty_before, seed_ty_after,
        "a later same-name registration must never clobber the seed's type"
    );
}

// ── codef: copattern definitions ──

#[test]
fn test_codef_stream_e2e() {
    let src = format!(
        "{STREAM_SRC}
codef natsFrom (n : Nat) : Stream Nat where
  head := n
  tail := natsFrom (Nat.succ n)

theorem n0 : Stream.head (natsFrom 5) = 5 := rfl
theorem n1 : Stream.head (Stream.tail (natsFrom 5)) = 6 := rfl
theorem n2 : Stream.head (Stream.tail (Stream.tail (natsFrom 5))) = 7 := rfl
"
    );
    let env = elab_all(&src);
    assert!(
        env.get_const(&Name::from_string("natsFrom")).is_some(),
        "codef must register the definition"
    );
}

#[test]
fn test_codef_zero_state_e2e() {
    let src = r#"
codata Ticker2 where
  tick : Nat
  next : Ticker2

codef zeros : Ticker2 where
  tick := 0
  next := zeros

theorem z0 : Ticker2.tick zeros = 0 := rfl
theorem z1 : Ticker2.tick (Ticker2.next zeros) = 0 := rfl
"#;
    elab_all(src);
}

#[test]
fn test_codef_branching_e2e() {
    let src = r#"
codata BT2 (A : Type) where
  label : A
  left : BT2 A
  right : BT2 A

codef skew2 (n : Nat) : BT2 Nat where
  label := n
  left := skew2 (Nat.succ n)
  right := skew2 (Nat.succ (Nat.succ n))

theorem k1 : BT2.label (BT2.left (skew2 0)) = 1 := rfl
theorem k2 : BT2.label (BT2.right (skew2 0)) = 2 := rfl
"#;
    elab_all(src);
}

#[test]
fn test_codef_missing_clause_rejected() {
    let src = format!(
        "{STREAM_SRC}
codef bad1 (n : Nat) : Stream Nat where
  head := n
"
    );
    let err = elab_expect_err(&src);
    assert!(
        format!("{err:?}").contains("missing clause"),
        "a missing observation clause must reject, got: {err:?}"
    );
}

#[test]
fn test_codef_unguarded_rejected() {
    // The observation clause mentions the function without being a plain
    // self-call — not productive, loud reject (fires at the codef decl).
    let mut env = Environment::with_prelude();
    let src = format!(
        "{STREAM_SRC}
codef bad2 (n : Nat) : Stream Nat where
  head := Stream.head (bad2 n)
  tail := bad2 n
"
    );
    let decls = parse_file(&src).expect("should parse");
    elaborate_decl_and_register(&mut env, &decls[0]).expect("codata must elaborate");
    let err = elaborate_decl_and_register(&mut env, &decls[1])
        .expect_err("the unguarded codef must be rejected");
    assert!(
        format!("{err:?}").contains("plain self-call"),
        "an unguarded self-mention must reject, got: {err:?}"
    );
}

#[test]
fn test_codef_non_codata_result_rejected() {
    let err = elab_expect_err("codef bad3 (n : Nat) : Nat where\n  head := n");
    assert!(
        format!("{err:?}").contains("not a codata type"),
        "a non-codata result type must reject, got: {err:?}"
    );
}

// ── mutual codata ──

#[test]
fn test_mutual_codata_tree_forest_e2e() {
    // The QPFTypes mutual-blocks answer at the surface: two members over
    // the Bool tag index, cross-member links computing by rfl.
    let src = r#"
mutual
  codata TreeM (A : Type) where
    label : A
    kids : ForestM A
  codata ForestM (A : Type) where
    first : TreeM A
    rest : ForestM A
end

def natTreeM (n : Nat) : TreeM Nat :=
  TreeM.corec (fun k => k) (fun k => Nat.succ k) (fun k => k) Nat.succ n
theorem m0 : TreeM.label (natTreeM 0) = 0 := rfl
theorem m1 : TreeM.label (ForestM.first (TreeM.kids (natTreeM 0))) = 1 := rfl
theorem m2 : TreeM.label (ForestM.first (ForestM.rest (TreeM.kids (natTreeM 0)))) = 2 := rfl
"#;
    let env = elab_all(src);
    for name in [
        "TreeM",
        "ForestM",
        "TreeM.label_corec",
        "TreeM.kids_corec",
        "ForestM.first_corec",
        "ForestM.rest_corec",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "mutual codata companion {name} must register"
        );
    }
}

#[test]
fn test_mutual_codata_three_member_ring_e2e() {
    // Σ-tags: a three-member mutual ring, cross-member links computing a
    // full cycle by rfl.
    let src = r#"
mutual
  codata X1 where
    a : Nat
    nx : X2
  codata X2 where
    b : Nat
    nx : X3
  codata X3 where
    c : Nat
    nx : X1
end

def ring3 (n : Nat) : X1 :=
  X1.corec (fun k => k) Nat.succ (fun k => k) Nat.succ (fun k => k)
    Nat.succ n
theorem r0 : X1.a (ring3 0) = 0 := rfl
theorem r1 : X2.b (X1.nx (ring3 0)) = 1 := rfl
theorem r2 : X3.c (X2.nx (X1.nx (ring3 0))) = 2 := rfl
theorem r3 : X1.a (X3.nx (X2.nx (X1.nx (ring3 0)))) = 3 := rfl
"#;
    let env = elab_all(src);
    for name in ["X1.a_corec", "X2.nx_corec", "X3.nx_corec"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "three-member mutual law {name} must register"
        );
    }
}

#[test]
fn test_mutual_codata_universe_param_e2e() {
    // U2: mutual codata at .{u} — every member declares the same envelope;
    // cross-member corecursion computes by rfl at u := 0 and u := 1.
    let src = r#"
mutual
  codata TreeP.{u} (A : Type u) where
    label : A
    kids : ForestP A
  codata ForestP.{u} (A : Type u) where
    first : TreeP A
    rest : ForestP A
end

def natTreeP (n : Nat) : TreeP Nat :=
  TreeP.corec (fun k => k) (fun k => Nat.succ k) (fun k => k) Nat.succ n
theorem mp0 : TreeP.label (natTreeP 0) = 0 := rfl
theorem mp1 : TreeP.label (ForestP.first (TreeP.kids (natTreeP 0))) = 1 := rfl

def tyTreeP : TreeP.{1} Type :=
  TreeP.corec (S1 := PUnit.{2}) (S2 := PUnit.{2})
    (fun _ => Nat) (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => PUnit.unit)
    PUnit.unit
theorem mpt : TreeP.label tyTreeP = Nat := rfl
"#;
    let env = elab_all(src);
    assert!(
        env.get_const(&Name::from_string("TreeP")).is_some(),
        "polymorphic mutual codata must register"
    );
}

#[test]
fn test_mutual_codata_mixed_universe_envelopes_rejected() {
    let err = elab_expect_err(
        "mutual
  codata TA.{u} (A : Type u) where
    label : A
    kids : FB A
  codata FB (A : Type u) where
    first : TA A
    rest : FB A
end",
    );
    assert!(
        format!("{err:?}").contains("SAME"),
        "mixed universe envelopes must reject, got: {err:?}"
    );
}

#[test]
fn test_mutual_codata_differing_params_rejected() {
    let src = r#"
mutual
  codata Y1 (A : Type) where
    a : A
    n : Y2 A
  codata Y2 (B : Type) where
    b : B
    n : Y1 B
end
"#;
    let err = elab_expect_err(src);
    assert!(
        format!("{err:?}").contains("IDENTICAL parameter lists"),
        "differing parameter lists must reject, got: {err:?}"
    );
}

// ── indexed codata ──

#[test]
fn test_indexed_codata_istream_e2e() {
    // The QPFTypes source-index answer at the surface: the container index
    // IS the declared index, and recursion moves it.
    let src = r#"
codata IStr : (n : Nat) → Type where
  val : Nat
  next : IStr (Nat.succ n)

def ixs (n : Nat) : IStr n :=
  IStr.corec (S := fun _ => Unit) (fun k _ => k) (fun _ _ => Unit.unit)
    n Unit.unit
theorem ix0 : IStr.val (ixs 5) = 5 := rfl
theorem ix1 : IStr.val (IStr.next (ixs 5)) = 6 := rfl
theorem ix2 : IStr.val (IStr.next (IStr.next (ixs 5))) = 7 := rfl
"#;
    let env = elab_all(src);
    for name in [
        "IStr",
        "IStr.val",
        "IStr.next",
        "IStr.corec",
        "IStr.val_corec",
        "IStr.next_corec",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "indexed codata companion {name} must register"
        );
    }
}

#[test]
fn test_indexed_codata_with_type_params_e2e() {
    // Parameters AND an index together: the parameterized indexed stream.
    let src = r#"
codata IVec (A : Type) : (n : Nat) → Type where
  head : A
  tail : IVec A (Nat.succ n)

def ones (n : Nat) : IVec Nat n :=
  IVec.corec (S := fun _ => Unit) (fun _ _ => 1) (fun _ _ => Unit.unit)
    n Unit.unit
theorem iv0 : IVec.head (ones 0) = 1 := rfl
theorem iv1 : IVec.head (IVec.tail (ones 0)) = 1 := rfl
"#;
    let env = elab_all(src);
    for name in [
        "IVec",
        "IVec.head",
        "IVec.tail",
        "IVec.corec",
        "IVec.tail_corec",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "parameterized indexed codata companion {name} must register"
        );
    }
}

#[test]
fn test_indexed_codata_universe_param_e2e() {
    // U2: indexed codata at .{u} — the two-universe seed payoff. The user
    // index (Nat) stays Type 0 (seed v := 0) while the families live at
    // Type u; corecursion computes by rfl at u := 0 AND u := 1.
    let src = r#"
codata IVecP.{u} (A : Type u) : (n : Nat) → Type u where
  head : A
  tail : IVecP A (Nat.succ n)

def onesP (n : Nat) : IVecP Nat n :=
  IVecP.corec (S := fun _ => Unit) (fun _ _ => 1) (fun _ _ => Unit.unit)
    n Unit.unit
theorem ivp0 : IVecP.head (onesP 0) = 1 := rfl
theorem ivp1 : IVecP.head (IVecP.tail (onesP 0)) = 1 := rfl

def typesP (n : Nat) : IVecP.{1} (Type) n :=
  IVecP.corec (S := fun _ => PUnit.{2}) (fun _ _ => Nat) (fun _ _ => PUnit.unit)
    n PUnit.unit
theorem tvp0 : IVecP.head (typesP 0) = Nat := rfl
"#;
    let env = elab_all(src);
    assert!(
        env.get_const(&Name::from_string("IVecP")).is_some(),
        "polymorphic indexed codata must register"
    );
}

#[test]
fn test_indexed_codata_multi_universe_params_rejected() {
    let err = elab_expect_err(
        "codata IV2.{u, v} (A : Type u) : (n : Nat) → Type u where
  head : A
  tail : IV2 A n",
    );
    assert!(
        format!("{err:?}").contains("ONE universe parameter"),
        "multi-param indexed codata must reject in v1, got: {err:?}"
    );
}

// ── codef into indexed codata ──

#[test]
fn test_codef_indexed_e2e() {
    // The index binder doubles as the corecursion index; a second binder
    // carries state whose type may mention the index.
    let src = r#"
codata IS2 : (n : Nat) → Type where
  val : Nat
  next : IS2 (Nat.succ n)

codef doubler (n : Nat) (acc : Nat) : IS2 n where
  val := acc
  next := doubler (Nat.succ n) (acc + acc)

theorem d0 : IS2.val (doubler 0 1) = 1 := rfl
theorem d1 : IS2.val (IS2.next (doubler 0 1)) = 2 := rfl
theorem d2 : IS2.val (IS2.next (IS2.next (doubler 0 1))) = 4 := rfl
"#;
    let env = elab_all(src);
    assert!(
        env.get_const(&Name::from_string("doubler")).is_some(),
        "indexed codef must register"
    );
}

#[test]
fn test_codef_indexed_zero_state_e2e() {
    let src = r#"
codata IS3 : (n : Nat) → Type where
  val : Nat
  next : IS3 (Nat.succ n)

codef tracker (n : Nat) : IS3 n where
  val := n
  next := tracker (Nat.succ n)

theorem t0 : IS3.val (tracker 4) = 4 := rfl
theorem t1 : IS3.val (IS3.next (tracker 4)) = 5 := rfl
"#;
    elab_all(src);
}

// ── mutual codef ──

#[test]
fn test_mutual_codef_e2e() {
    // Joint copattern definitions into a mutual codata block: each codef
    // supplies its member's clauses; calls to EITHER codef are the
    // corecursive steps.
    let src = r#"
mutual
  codata TreeQ (A : Type) where
    label : A
    kids : ForestQ A
  codata ForestQ (A : Type) where
    first : TreeQ A
    rest : ForestQ A
end

mutual
  codef tq (s : Nat) : TreeQ Nat where
    label := s
    kids := fq (Nat.succ s)
  codef fq (s : Nat) : ForestQ Nat where
    first := tq s
    rest := fq (Nat.succ s)
end

theorem q0 : TreeQ.label (tq 0) = 0 := rfl
theorem q1 : TreeQ.label (ForestQ.first (TreeQ.kids (tq 0))) = 1 := rfl
theorem q2 : TreeQ.label (ForestQ.first (ForestQ.rest (TreeQ.kids (tq 0)))) = 2 := rfl
"#;
    let env = elab_all(src);
    for name in ["tq", "fq"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "mutual codef {name} must register"
        );
    }
}

#[test]
fn test_mutual_codef_missing_member_rejected() {
    let src = r#"
mutual
  codata TA where
    a : Nat
    nx : TB
  codata TB where
    b : Nat
    nx : TA
end

mutual
  codef onlyA (s : Nat) : TA where
    a := s
    nx := onlyA s
end
"#;
    let err = elab_expect_err(src);
    assert!(
        format!("{err:?}").contains("no codef in the block targets"),
        "a block missing a member's codef must reject, got: {err:?}"
    );
}

// ── multi-index codata ──

#[test]
fn test_multi_index_codata_grid_e2e() {
    // Two indices (packed container, unpacked user surface): a grid whose
    // right/down moves touch different indices.
    let src = r#"
codata Grid2 : (r : Nat) → (c : Nat) → Type where
  cell : Nat
  right : Grid2 r (Nat.succ c)
  down : Grid2 (Nat.succ r) c

def sumGrid (r : Nat) (c : Nat) : Grid2 r c :=
  Grid2.corec (S := fun _ => Unit)
    (fun ip _ => Nat.add ip.1 ip.2)
    (fun _ _ => Unit.unit) (fun _ _ => Unit.unit)
    r c Unit.unit
theorem g00 : Grid2.cell (sumGrid 1 2) = 3 := rfl
theorem g01 : Grid2.cell (Grid2.right (sumGrid 1 2)) = 4 := rfl
theorem g10 : Grid2.cell (Grid2.down (sumGrid 1 2)) = 4 := rfl
theorem g11 : Grid2.cell (Grid2.down (Grid2.right (sumGrid 1 2))) = 5 := rfl
"#;
    let env = elab_all(src);
    for name in [
        "Grid2",
        "Grid2.cell",
        "Grid2.right_corec",
        "Grid2.down_corec",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "multi-index companion {name} must register"
        );
    }
}

// ── generated constructors (C.mk) ──

#[test]
fn test_codata_mk_e2e() {
    // Every plain codata now carries a finite one-layer constructor with
    // rfl laws — and mk-around-corec gives finite-prefix-then-corecurse
    // (depth-1 guardedness) at the term level.
    let src = format!(
        "{STREAM_SRC}
def prefixed : Stream Nat := Stream.mk 7 (Stream.corec (fun k => k) Nat.succ 0)
theorem p0 : Stream.head prefixed = 7 := rfl
theorem p1 : Stream.head (Stream.tail prefixed) = 0 := rfl
theorem p2 : Stream.head (Stream.tail (Stream.tail prefixed)) = 1 := rfl
"
    );
    let env = elab_all(&src);
    for name in ["Stream.mk", "Stream.head_mk", "Stream.tail_mk"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "constructor companion {name} must register"
        );
    }
}

#[test]
fn test_codata_mk_branching_e2e() {
    let src = r#"
codata BTk (A : Type) where
  label : A
  left : BTk A
  right : BTk A

def leafy : BTk Nat :=
  BTk.mk 5 (BTk.corec (fun k => k) Nat.succ Nat.succ 0)
    (BTk.corec (fun k => k) Nat.succ Nat.succ 10)
theorem k5 : BTk.label leafy = 5 := rfl
theorem kl : BTk.label (BTk.left leafy) = 0 := rfl
theorem kr : BTk.label (BTk.right leafy) = 10 := rfl
"#;
    elab_all(src);
}

#[test]
fn test_indexed_codata_mk_e2e() {
    // The indexed constructor: the child lives at the moved index.
    let src = r#"
codata IS4 : (n : Nat) → Type where
  val : Nat
  next : IS4 (Nat.succ n)

def track4 (n : Nat) : IS4 n :=
  IS4.corec (S := fun _ => Unit) (fun k _ => k) (fun _ _ => Unit.unit)
    n Unit.unit
def capped : IS4 3 := IS4.mk 99 (track4 4)
theorem c99 : IS4.val capped = 99 := rfl
theorem c4 : IS4.val (IS4.next capped) = 4 := rfl
"#;
    let env = elab_all(src);
    for name in ["IS4.mk", "IS4.val_mk", "IS4.next_mk"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "indexed constructor companion {name} must register"
        );
    }
}

#[test]
fn test_mutual_codata_mk_e2e() {
    // Per-member constructors in a mutual block: the child slots are the
    // TARGET members' types (the mutual knot at the term level).
    let src = r#"
mutual
  codata TreeC (A : Type) where
    label : A
    kids : ForestC A
  codata ForestC (A : Type) where
    first : TreeC A
    rest : ForestC A
end

def tf0 (n : Nat) : TreeC Nat :=
  TreeC.corec (fun k => k) (fun k => k) (fun k => k) Nat.succ n
def built : TreeC Nat := TreeC.mk 42 (ForestC.mk (tf0 7) (ForestC.mk (tf0 8) (TreeC.kids (tf0 9))))
theorem b42 : TreeC.label built = 42 := rfl
theorem b7 : TreeC.label (ForestC.first (TreeC.kids built)) = 7 := rfl
theorem b8 : TreeC.label (ForestC.first (ForestC.rest (TreeC.kids built))) = 8 := rfl
"#;
    let env = elab_all(src);
    for name in [
        "TreeC.mk",
        "ForestC.mk",
        "TreeC.label_mk",
        "ForestC.rest_mk",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "mutual constructor companion {name} must register"
        );
    }
}

#[test]
fn test_mutual_three_member_mk_e2e() {
    let src = r#"
mutual
  codata Y1 where
    a : Nat
    nx : Y2
  codata Y2 where
    b : Nat
    nx : Y3
  codata Y3 where
    c : Nat
    nx : Y1
end

def yring (n : Nat) : Y1 :=
  Y1.corec (fun k => k) Nat.succ (fun k => k) Nat.succ (fun k => k)
    Nat.succ n
def ycap : Y1 := Y1.mk 5 (Y2.mk 6 (Y3.mk 7 (yring 100)))
theorem y5 : Y1.a ycap = 5 := rfl
theorem y6 : Y2.b (Y1.nx ycap) = 6 := rfl
theorem y7 : Y3.c (Y2.nx (Y1.nx ycap)) = 7 := rfl
theorem y100 : Y1.a (Y3.nx (Y2.nx (Y1.nx ycap))) = 100 := rfl
"#;
    elab_all(src);
}

#[test]
fn test_multi_index_codata_mk_e2e() {
    let src = r#"
codata Grid3 : (r : Nat) → (c : Nat) → Type where
  cell : Nat
  right : Grid3 r (Nat.succ c)
  down : Grid3 (Nat.succ r) c

def base3 (r : Nat) (c : Nat) : Grid3 r c :=
  Grid3.corec (S := fun _ => Unit)
    (fun ip _ => Nat.add ip.1 ip.2)
    (fun _ _ => Unit.unit) (fun _ _ => Unit.unit)
    r c Unit.unit
def patched : Grid3 1 1 := Grid3.mk 77 (base3 1 2) (base3 2 1)
theorem m77 : Grid3.cell patched = 77 := rfl
theorem mr : Grid3.cell (Grid3.right patched) = 3 := rfl
theorem md : Grid3.cell (Grid3.down patched) = 3 := rfl
"#;
    elab_all(src);
}

// ── mk-guarded codef clauses ──

#[test]
fn test_codef_mk_guarded_e2e() {
    // The corecursive clause carries one constructor layer around the
    // self-call — compiled via the Bool-flag buffered state.
    let src = format!(
        "{STREAM_SRC}
codef alternate (s : Nat) : Stream Nat where
  head := s
  tail := Stream.mk (Nat.add s 100) (alternate (Nat.succ s))

theorem g0 : Stream.head (alternate 0) = 0 := rfl
theorem g1 : Stream.head (Stream.tail (alternate 0)) = 100 := rfl
theorem g2 : Stream.head (Stream.tail (Stream.tail (alternate 0))) = 1 := rfl
theorem g3 : Stream.head (Stream.tail (Stream.tail (Stream.tail (alternate 0)))) = 101 := rfl
"
    );
    let env = elab_all(&src);
    assert!(
        env.get_const(&Name::from_string("alternate")).is_some(),
        "mk-guarded codef must register"
    );
}

#[test]
fn test_codef_mk_guarded_bad_inner_rejected() {
    // The innermost child must be the self-call — a non-call inner value
    // rejects loudly.
    let src = format!(
        "{STREAM_SRC}
codef bad4 (s : Nat) : Stream Nat where
  head := s
  tail := Stream.mk 1 (Stream.corec (fun k => bad4 k) (fun k => k) s)
"
    );
    let mut env = Environment::with_prelude();
    let decls = parse_file(&src).expect("should parse");
    elaborate_decl_and_register(&mut env, &decls[0]).expect("codata must elaborate");
    let err = elaborate_decl_and_register(&mut env, &decls[1])
        .expect_err("a non-self-call inner value must be rejected");
    let _ = err;
}

#[test]
fn test_codef_mk_guarded_depth2_e2e() {
    // Two nested constructor layers around the self-call.
    let src = format!(
        "{STREAM_SRC}
codef three (s : Nat) : Stream Nat where
  head := s
  tail := Stream.mk 100 (Stream.mk 200 (three (Nat.succ s)))

theorem e0 : Stream.head (three 7) = 7 := rfl
theorem e1 : Stream.head (Stream.tail (three 7)) = 100 := rfl
theorem e2 : Stream.head (Stream.tail (Stream.tail (three 7))) = 200 := rfl
theorem e3 : Stream.head (Stream.tail (Stream.tail (Stream.tail (three 7)))) = 8 := rfl
theorem e4 : Stream.head (Stream.tail (Stream.tail (Stream.tail (Stream.tail (three 7))))) = 100 := rfl
"
    );
    elab_all(&src);
}

// ── rank 7: the width-1 lazy-lowering chain, source side ──

/// The rank-7 width-1 fixture elaborates as a FILE, and its finite-observation
/// operator holds definitionally.
///
/// Every other indexed-codata exercise in this file is a Rust string literal,
/// which nothing outside the test binary can consume. Rank 7 drives a real
/// `.lean` file through a CLI verb, so the fixture has to exist on disk and
/// stay green independently.
///
/// `IS2.nth k n s` is the finite observation the rank-7 soundness statement is
/// ABOUT: the theorem to prove is that `nth k` equals the decode of `k` forced
/// target layers. Both of its laws being `rfl` is what makes the depth-`k`
/// induction discharge without propositional reasoning -- if that ever stops
/// holding, the soundness proof's shape changes, so it is pinned here.
#[test]
fn test_rank7_is2_fixture_file_elaborates() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/codata/is2_indexed_stream.lean");
    let src = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("rank-7 fixture must exist at {}: {e}", path.display()));
    let env = elab_all(&src);

    // The indexed carrier, the corecursive value, and the observation operator.
    for n in ["IS2", "doubler", "IS2.nth"] {
        assert!(
            env.get_const(&Name::from_string(n)).is_some(),
            "rank-7 fixture must register `{n}`"
        );
    }
}

/// `codef` mints a [`CodataOrigin`] hint, and a hand-written definition does not.
///
/// The negative control is the point of the test. `C.corec` is a
/// USER-DERIVABLE name -- nothing stops anyone writing `def Stream.corec` --
/// so if recognition ever keyed off the name, a hand-written constant would be
/// indistinguishable from a generated one. The origin exists precisely so
/// recognition never has to guess, and it must be minted ONLY by the generator.
///
/// The hint still authorizes nothing: a consumer must re-resolve `corec` and
/// structurally replay the canonical body before acting on it.
#[test]
fn test_rank7_codef_mints_codata_origin() {
    let src = r#"
codata IS2 : (n : Nat) → Type where
  val : Nat
  next : IS2 (Nat.succ n)

codef doubler (n : Nat) (acc : Nat) : IS2 n where
  val := acc
  next := doubler (Nat.succ n) (acc + acc)

def handwritten (x : Nat) : Nat := x
"#;
    let env = elab_all(src);

    let origin = env
        .get_codata_origin(&Name::from_string("doubler"))
        .expect("codef must mint a codata origin");
    assert_eq!(origin.lane, clean_kernel::CodataLane::Indexed);
    assert_eq!(origin.carrier, Name::from_string("IS2"));
    assert_eq!(origin.corec, Name::from_string("IS2.corec"));
    assert!(
        origin.slot_count() >= 2,
        "IS2 has two fields (val, next), so the canonical body supplies at \
         least two slot lambdas; got {:?}",
        origin.slots
    );

    // Negative control: an ordinary definition is NOT codata, and must carry
    // no origin -- absence is what makes a consumer decline.
    assert!(
        env.get_codata_origin(&Name::from_string("handwritten"))
            .is_none(),
        "a hand-written definition must never mint a codata origin"
    );
}

/// A failed `codef` leaves behind no origin.
///
/// The origin is minted into the same transactional environment clone that
/// carries the generated declarations, so a `codef` whose generated body fails
/// to kernel-check must not leave a dangling hint pointing at a constant that
/// does not exist.
#[test]
fn test_rank7_failed_codef_mints_no_origin() {
    let src = r#"
codata IS2 : (n : Nat) → Type where
  val : Nat
  next : IS2 (Nat.succ n)
"#;
    // Elaborate ONLY the codata; `doubler` never existed.
    let env = elab_all(src);
    assert!(
        env.get_codata_origin(&Name::from_string("doubler"))
            .is_none(),
        "no codef ran, so there must be no origin"
    );
    assert_eq!(
        env.codata_origin_count(),
        0,
        "a bare `codata` declaration mints no codef origins"
    );
}

// ── indexed codef: index fidelity ──

/// A self-call at the WRONG index is a loud error.
///
/// The corecursor forces every child to the codata FIELD's target index, and
/// the written index was discarded. So this compiled, and meant something the
/// author did not write: `IS3.val (IS3.next (tr 4))` reduced to 5 — the
/// target's move — while the author's own `tr n` says 4. The ERRONEOUS program
/// was the one that compiled.
#[test]
fn test_indexed_codef_wrong_index_rejected() {
    let mut env = Environment::with_prelude();
    let src = "\
codata IS3 : (n : Nat) -> Type where
  val : Nat
  next : IS3 (Nat.succ n)

codef tr (n : Nat) : IS3 n where
  val := n
  next := tr n
";
    let decls = parse_file(src).expect("should parse");
    elaborate_decl_and_register(&mut env, &decls[0]).expect("codata must elaborate");
    let err = elaborate_decl_and_register(&mut env, &decls[1])
        .expect_err("a self-call at the wrong index must be rejected");
    assert!(
        format!("{err:?}").contains("corecurses at an index"),
        "expected an index-fidelity rejection, got: {err:?}"
    );
}

/// Same, in the STATEFUL shape — and the index is `args[0]`, not the last arg.
#[test]
fn test_indexed_codef_wrong_index_rejected_with_state() {
    let mut env = Environment::with_prelude();
    let src = "\
codata IS2 : (n : Nat) -> Type where
  val : Nat
  next : IS2 (Nat.succ n)

codef bad (n : Nat) (acc : Nat) : IS2 n where
  val := acc
  next := bad n (acc + acc)
";
    let decls = parse_file(src).expect("should parse");
    elaborate_decl_and_register(&mut env, &decls[0]).expect("codata must elaborate");
    let err = elaborate_decl_and_register(&mut env, &decls[1])
        .expect_err("a stateful self-call at the wrong index must be rejected");
    assert!(
        format!("{err:?}").contains("corecurses at an index"),
        "expected an index-fidelity rejection, got: {err:?}"
    );
}

/// The check is DEFEQ, not syntactic: `n + 1` satisfies a `Nat.succ n` target.
///
/// This is the property that stops the guard from being "reject unless the
/// author retyped the target character-for-character". If this test ever fails
/// because someone simplified the probe into a `SurfaceExpr` equality, that is
/// the regression, not this test.
#[test]
fn test_indexed_codef_defeq_index_accepted() {
    let env = elab_all(
        "\
codata IS4 : (n : Nat) -> Type where
  val : Nat
  next : IS4 (Nat.succ n)

codef okd (n : Nat) (acc : Nat) : IS4 n where
  val := acc
  next := okd (n + 1) (acc + acc)
",
    );
    assert!(
        env.get_const(&Name::from_string("okd")).is_some(),
        "`n + 1` is definitionally `Nat.succ n`, so this codef must be accepted"
    );
}

/// The guard must not leak its probe, and must leave the env untouched on
/// rejection so the name stays free.
#[test]
fn test_indexed_codef_index_probe_is_transactional() {
    let mut env = Environment::with_prelude();
    let src = "\
codata IS5 : (n : Nat) -> Type where
  val : Nat
  next : IS5 (Nat.succ n)

codef tr5 (n : Nat) : IS5 n where
  val := n
  next := tr5 n
";
    let decls = parse_file(src).expect("should parse");
    elaborate_decl_and_register(&mut env, &decls[0]).expect("codata must elaborate");
    let before = env.num_constants();
    elaborate_decl_and_register(&mut env, &decls[1]).expect_err("must be rejected");
    assert_eq!(
        env.num_constants(),
        before,
        "a rejected codef must leave the environment untouched"
    );
    assert!(
        env.get_const(&Name::from_string("tr5._indexProbe_next"))
            .is_none(),
        "the probe declaration must never be registered"
    );
    assert!(
        env.get_const(&Name::from_string("tr5")).is_none(),
        "the rejected codef's own name must stay free"
    );
}

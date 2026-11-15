// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Relation-polymorphic star, join and union metatheory.
//! Normalized tuples from registration.5VlASb; Union endpoints are explicit
//! parameters. The diamond's constructor maps are eta-expanded for actual
//! expected-type elaboration; theorem statements and relation colors are unchanged.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Inductive(
        r"inductive RelationStar (A : Type) (R : A -> A -> Type) : A -> A -> Type
| refl : forall (a : A), RelationStar A R a a
| step : forall (a b c : A), R a b -> RelationStar A R b c -> RelationStar A R a c",
    ),
    DeclarationInput::Inductive(
        r"inductive RelationJoin (A : Type) (R S : A -> A -> Type) (a b : A) : Type
| mk : forall (c : A), R a c -> S b c -> RelationJoin A R S a b",
    ),
    DeclarationInput::Inductive(
        r"inductive RelationUnion (A : Type) (R S : A -> A -> Type) (a b : A) : Type
| left : R a b -> RelationUnion A R S a b
| right : S a b -> RelationUnion A R S a b",
    ),
    DeclarationInput::Proof(
        "relation_star_single",
        r"forall (A : Type) (R : A -> A -> Type)
 (a b : A) (h : R a b), RelationStar A R a b",
        r"fun (A : Type) (R : A -> A -> Type)
 (a b : A) (h : R a b) => @RelationStar.step A R a b b h (@RelationStar.refl A R b)",
    ),
    DeclarationInput::Proof(
        "relation_star_trans",
        r"forall (A : Type) (R : A -> A -> Type)
 (a b c : A) (ab : RelationStar A R a b) (bc : RelationStar A R b c), RelationStar A R a c",
        r"fun (A : Type) (R : A -> A -> Type)
 (a b c : A) (ab : RelationStar A R a b) (bc : RelationStar A R b c) => @RelationStar.rec A R
  (fun (x y : A) (_ : RelationStar A R x y) =>
   RelationStar A R y c -> RelationStar A R x c)
  (fun (x : A) (h : RelationStar A R x c) => h)
  (fun (x y z : A) (xy : R x y) (_ : RelationStar A R y z)
   (ih : RelationStar A R z c -> RelationStar A R y c)
   (h : RelationStar A R z c) => @RelationStar.step A R x y c xy (ih h))
  a b ab bc",
    ),
    DeclarationInput::Proof(
        "relation_star_bind",
        r"forall (A : Type) (R S : A -> A -> Type)
 (embed : forall (x y : A), R x y -> RelationStar A S x y)
 (a b : A) (h : RelationStar A R a b), RelationStar A S a b",
        r"fun (A : Type) (R S : A -> A -> Type)
 (embed : forall (x y : A), R x y -> RelationStar A S x y)
 (a b : A) (h : RelationStar A R a b) => @RelationStar.rec A R
  (fun (x y : A) (_ : RelationStar A R x y) => RelationStar A S x y)
  (fun (x : A) => @RelationStar.refl A S x)
  (fun (x y z : A) (xy : R x y) (_ : RelationStar A R y z)
   (ih : RelationStar A S y z) => relation_star_trans A S x y z (embed x y xy) ih)
  a b h",
    ),
    DeclarationInput::Proof(
        "relation_join_map",
        r"forall (A : Type) (R S T U : A -> A -> Type)
 (left : forall (x y : A), R x y -> T x y)
 (right : forall (x y : A), S x y -> U x y)
 (a b : A) (h : RelationJoin A R S a b), RelationJoin A T U a b",
        r"fun (A : Type) (R S T U : A -> A -> Type)
 (left : forall (x y : A), R x y -> T x y)
 (right : forall (x y : A), S x y -> U x y)
 (a b : A) (h : RelationJoin A R S a b) => @RelationJoin.rec A R S a b
  (fun (_ : RelationJoin A R S a b) => RelationJoin A T U a b)
  (fun (c : A) (ac : R a c) (bc : S b c) =>
   @RelationJoin.mk A T U a b c (left a c ac) (right b c bc)) h",
    ),
    DeclarationInput::Proof(
        "relation_join_swap",
        r"forall (A : Type) (R S : A -> A -> Type)
 (a b : A) (h : RelationJoin A R S a b), RelationJoin A S R b a",
        r"fun (A : Type) (R S : A -> A -> Type)
 (a b : A) (h : RelationJoin A R S a b) => @RelationJoin.rec A R S a b
  (fun (_ : RelationJoin A R S a b) => RelationJoin A S R b a)
  (fun (c : A) (ac : R a c) (bc : S b c) => @RelationJoin.mk A S R b a c bc ac) h",
    ),
    DeclarationInput::Proof(
        "relation_diamond_strip",
        r"forall (A : Type) (R : A -> A -> Type)
 (diamond : forall (e a b : A), R e a -> R e b -> RelationJoin A R R a b)
 (e a b : A) (ea : R e a) (eb : RelationStar A R e b), RelationJoin A (RelationStar A R) R a b",
        r"fun (A : Type) (R : A -> A -> Type)
 (diamond : forall (e a b : A), R e a -> R e b -> RelationJoin A R R a b)
 (e a b : A) (ea : R e a) (eb : RelationStar A R e b) => @RelationStar.rec A R
  (fun (x y : A) (_ : RelationStar A R x y) =>
   forall (u : A), R x u -> RelationJoin A (RelationStar A R) R u y)
  (fun (x u : A) (xu : R x u) =>
   @RelationJoin.mk A (RelationStar A R) R u x u (@RelationStar.refl A R u) xu)
  (fun (x y z : A) (xy : R x y) (_ : RelationStar A R y z)
   (ih : forall (u : A), R y u -> RelationJoin A (RelationStar A R) R u z)
   (u : A) (xu : R x u) =>
   @RelationJoin.rec A R R u y
    (fun (_ : RelationJoin A R R u y) => RelationJoin A (RelationStar A R) R u z)
    (fun (v : A) (uv : R u v) (yv : R y v) =>
     @RelationJoin.rec A (RelationStar A R) R v z
      (fun (_ : RelationJoin A (RelationStar A R) R v z) =>
       RelationJoin A (RelationStar A R) R u z)
      (fun (w : A) (vw : RelationStar A R v w) (zw : R z w) =>
       @RelationJoin.mk A (RelationStar A R) R u z w (@RelationStar.step A R u v w uv vw) zw)
      (ih v yv)) (diamond x u y xu xy))
  e b eb a ea",
    ),
    DeclarationInput::Proof(
        "relation_diamond_confluent",
        r"forall (A : Type) (R : A -> A -> Type)
 (diamond : forall (e a b : A), R e a -> R e b -> RelationJoin A R R a b)
 (e a b : A) (ea : RelationStar A R e a) (eb : RelationStar A R e b), RelationJoin A (RelationStar A R) (RelationStar A R) a b",
        r"fun (A : Type) (R : A -> A -> Type)
 (diamond : forall (e a b : A), R e a -> R e b -> RelationJoin A R R a b)
 (e a b : A) (ea : RelationStar A R e a) (eb : RelationStar A R e b) => @RelationStar.rec A R
  (fun (x y : A) (_ : RelationStar A R x y) =>
   forall (z : A), RelationStar A R x z ->
    RelationJoin A (RelationStar A R) (RelationStar A R) y z)
  (fun (x z : A) (xz : RelationStar A R x z) =>
   @RelationJoin.mk A (RelationStar A R) (RelationStar A R) x z z xz (@RelationStar.refl A R z))
  (fun (x y z : A) (xy : R x y) (_ : RelationStar A R y z)
   (ih : forall (u : A), RelationStar A R y u ->
    RelationJoin A (RelationStar A R) (RelationStar A R) z u)
   (v : A) (xv : RelationStar A R x v) =>
   @RelationJoin.rec A (RelationStar A R) R y v
    (fun (_ : RelationJoin A (RelationStar A R) R y v) =>
     RelationJoin A (RelationStar A R) (RelationStar A R) z v)
    (fun (w : A) (yw : RelationStar A R y w) (vw : R v w) =>
     @RelationJoin.rec A (RelationStar A R) (RelationStar A R) z w
      (fun (_ : RelationJoin A (RelationStar A R) (RelationStar A R) z w) =>
       RelationJoin A (RelationStar A R) (RelationStar A R) z v)
      (fun (q : A) (zq : RelationStar A R z q) (wq : RelationStar A R w q) =>
       @RelationJoin.mk A (RelationStar A R) (RelationStar A R) z v q zq
        (@RelationStar.step A R v w q vw wq)) (ih w yw))
    (relation_diamond_strip A R diamond x y v xy xv))
  e a ea b eb",
    ),
    DeclarationInput::Proof(
        "relation_union_diamond",
        r"forall (A : Type) (R S : A -> A -> Type)
 (dr : forall (e a b : A), R e a -> R e b -> RelationJoin A R R a b)
 (ds : forall (e a b : A), S e a -> S e b -> RelationJoin A S S a b)
 (comm : forall (e a b : A), R e a -> S e b -> RelationJoin A S R a b)
 (e a b : A) (ea : RelationUnion A R S e a) (eb : RelationUnion A R S e b), RelationJoin A (RelationUnion A R S) (RelationUnion A R S) a b",
        r"fun (A : Type) (R S : A -> A -> Type)
 (dr : forall (e a b : A), R e a -> R e b -> RelationJoin A R R a b)
 (ds : forall (e a b : A), S e a -> S e b -> RelationJoin A S S a b)
 (comm : forall (e a b : A), R e a -> S e b -> RelationJoin A S R a b)
 (e a b : A) (ea : RelationUnion A R S e a) (eb : RelationUnion A R S e b) => RelationUnion.rec A R S e a
 (fun (_union_witness : RelationUnion A R S e a) => (fun (x y : A) (_ : RelationUnion A R S x y) =>
   forall (z : A), RelationUnion A R S x z ->
    RelationJoin A (RelationUnion A R S) (RelationUnion A R S) y z) e a _union_witness)
 (fun (_union_left : R e a) => (fun (x y : A) (xy : R x y) (z : A) (xz : RelationUnion A R S x z) =>
   RelationUnion.rec A R S x z
 (fun (_union_witness : RelationUnion A R S x z) => (fun (u v : A) (_ : RelationUnion A R S u v) =>
     R u y -> RelationJoin A (RelationUnion A R S) (RelationUnion A R S) y v) x z _union_witness)
 (fun (_union_left : R x z) => (fun (u v : A) (uv : R u v) (uy : R u y) =>
     relation_join_map A R R (RelationUnion A R S) (RelationUnion A R S)
      (fun (union_map_source union_map_target : A) (union_map_edge : R union_map_source union_map_target) => @RelationUnion.left A R S union_map_source union_map_target union_map_edge) (fun (union_map_source union_map_target : A) (union_map_edge : R union_map_source union_map_target) => @RelationUnion.left A R S union_map_source union_map_target union_map_edge) y v (dr u y v uy uv)) x z _union_left)
 (fun (_union_right : S x z) => (fun (u v : A) (uv : S u v) (uy : R u y) =>
     relation_join_map A S R (RelationUnion A R S) (RelationUnion A R S)
      (fun (union_map_source union_map_target : A) (union_map_edge : S union_map_source union_map_target) => @RelationUnion.right A R S union_map_source union_map_target union_map_edge) (fun (union_map_source union_map_target : A) (union_map_edge : R union_map_source union_map_target) => @RelationUnion.left A R S union_map_source union_map_target union_map_edge) y v (comm u y v uy uv)) x z _union_right)
 xz xy) e a _union_left)
 (fun (_union_right : S e a) => (fun (x y : A) (xy : S x y) (z : A) (xz : RelationUnion A R S x z) =>
   RelationUnion.rec A R S x z
 (fun (_union_witness : RelationUnion A R S x z) => (fun (u v : A) (_ : RelationUnion A R S u v) =>
     S u y -> RelationJoin A (RelationUnion A R S) (RelationUnion A R S) y v) x z _union_witness)
 (fun (_union_left : R x z) => (fun (u v : A) (uv : R u v) (uy : S u y) =>
     relation_join_map A R S (RelationUnion A R S) (RelationUnion A R S)
      (fun (union_map_source union_map_target : A) (union_map_edge : R union_map_source union_map_target) => @RelationUnion.left A R S union_map_source union_map_target union_map_edge) (fun (union_map_source union_map_target : A) (union_map_edge : S union_map_source union_map_target) => @RelationUnion.right A R S union_map_source union_map_target union_map_edge) y v
      (relation_join_swap A S R v y (comm u v y uv uy))) x z _union_left)
 (fun (_union_right : S x z) => (fun (u v : A) (uv : S u v) (uy : S u y) =>
     relation_join_map A S S (RelationUnion A R S) (RelationUnion A R S)
      (fun (union_map_source union_map_target : A) (union_map_edge : S union_map_source union_map_target) => @RelationUnion.right A R S union_map_source union_map_target union_map_edge) (fun (union_map_source union_map_target : A) (union_map_edge : S union_map_source union_map_target) => @RelationUnion.right A R S union_map_source union_map_target union_map_edge) y v (ds u y v uy uv)) x z _union_right)
 xz xy) e a _union_right)
 ea b eb",
    ),
    DeclarationInput::Proof(
        "relation_union_to_macro",
        r"forall (A : Type) (R S : A -> A -> Type)
 (a b : A) (h : RelationStar A (RelationUnion A R S) a b), RelationStar A (RelationUnion A (RelationStar A R) (RelationStar A S)) a b",
        r"fun (A : Type) (R S : A -> A -> Type)
 (a b : A) (h : RelationStar A (RelationUnion A R S) a b) => relation_star_bind A (RelationUnion A R S)
  (RelationUnion A (RelationStar A R) (RelationStar A S))
  (fun (x y : A) (xy : RelationUnion A R S x y) =>
   RelationUnion.rec A R S x y
 (fun (_union_witness : RelationUnion A R S x y) => (fun (u v : A) (_ : RelationUnion A R S u v) =>
     RelationStar A (RelationUnion A (RelationStar A R) (RelationStar A S)) u v) x y _union_witness)
 (fun (_union_left : R x y) => (fun (u v : A) (uv : R u v) =>
     relation_star_single A (RelationUnion A (RelationStar A R) (RelationStar A S)) u v
      (@RelationUnion.left A (RelationStar A R) (RelationStar A S) u v (relation_star_single A R u v uv))) x y _union_left)
 (fun (_union_right : S x y) => (fun (u v : A) (uv : S u v) =>
     relation_star_single A (RelationUnion A (RelationStar A R) (RelationStar A S)) u v
      (@RelationUnion.right A (RelationStar A R) (RelationStar A S) u v (relation_star_single A S u v uv))) x y _union_right)
 xy) a b h",
    ),
    DeclarationInput::Proof(
        "relation_macro_to_union",
        r"forall (A : Type) (R S : A -> A -> Type)
 (a b : A) (h : RelationStar A (RelationUnion A (RelationStar A R) (RelationStar A S)) a b), RelationStar A (RelationUnion A R S) a b",
        r"fun (A : Type) (R S : A -> A -> Type)
 (a b : A) (h : RelationStar A (RelationUnion A (RelationStar A R) (RelationStar A S)) a b) => relation_star_bind A (RelationUnion A (RelationStar A R) (RelationStar A S)) (RelationUnion A R S)
  (fun (x y : A) (xy : RelationUnion A (RelationStar A R) (RelationStar A S) x y) =>
   RelationUnion.rec A (RelationStar A R) (RelationStar A S) x y
 (fun (_union_witness : RelationUnion A (RelationStar A R) (RelationStar A S) x y) => (fun (u v : A) (_ : RelationUnion A (RelationStar A R) (RelationStar A S) u v) =>
     RelationStar A (RelationUnion A R S) u v) x y _union_witness)
 (fun (_union_left : (RelationStar A R) x y) => (fun (u v : A) (uv : RelationStar A R u v) =>
     relation_star_bind A R (RelationUnion A R S)
      (fun (p q : A) (pq : R p q) =>
       relation_star_single A (RelationUnion A R S) p q (@RelationUnion.left A R S p q pq)) u v uv) x y _union_left)
 (fun (_union_right : (RelationStar A S) x y) => (fun (u v : A) (uv : RelationStar A S u v) =>
     relation_star_bind A S (RelationUnion A R S)
      (fun (p q : A) (pq : S p q) =>
       relation_star_single A (RelationUnion A R S) p q (@RelationUnion.right A R S p q pq)) u v uv) x y _union_right)
 xy) a b h",
    ),
    DeclarationInput::Proof(
        "relation_strong_commute_strip",
        r"forall (A : Type) (R S : A -> A -> Type)
 (sc : forall (e a b : A), R e a -> S e b -> RelationJoin A (RelationStar A S) R a b)
 (e a b : A) (ea : R e a) (eb : RelationStar A S e b), RelationJoin A (RelationStar A S) R a b",
        r"fun (A : Type) (R S : A -> A -> Type)
 (sc : forall (e a b : A), R e a -> S e b -> RelationJoin A (RelationStar A S) R a b)
 (e a b : A) (ea : R e a) (eb : RelationStar A S e b) => @RelationStar.rec A S
  (fun (x y : A) (_ : RelationStar A S x y) =>
   forall (u : A), R x u -> RelationJoin A (RelationStar A S) R u y)
  (fun (x u : A) (xu : R x u) =>
   @RelationJoin.mk A (RelationStar A S) R u x u (@RelationStar.refl A S u) xu)
  (fun (x y z : A) (xy : S x y) (_ : RelationStar A S y z)
   (ih : forall (u : A), R y u -> RelationJoin A (RelationStar A S) R u z)
   (u : A) (xu : R x u) =>
   @RelationJoin.rec A (RelationStar A S) R u y
    (fun (_ : RelationJoin A (RelationStar A S) R u y) =>
     RelationJoin A (RelationStar A S) R u z)
    (fun (v : A) (uv : RelationStar A S u v) (yv : R y v) =>
     @RelationJoin.rec A (RelationStar A S) R v z
      (fun (_ : RelationJoin A (RelationStar A S) R v z) =>
       RelationJoin A (RelationStar A S) R u z)
      (fun (w : A) (vw : RelationStar A S v w) (zw : R z w) =>
       @RelationJoin.mk A (RelationStar A S) R u z w
        (relation_star_trans A S u v w uv vw) zw) (ih v yv)) (sc x u y xu xy))
  e b eb a ea",
    ),
    DeclarationInput::Proof(
        "relation_strong_commute_star",
        r"forall (A : Type) (R S : A -> A -> Type)
 (sc : forall (e a b : A), R e a -> S e b -> RelationJoin A (RelationStar A S) R a b)
 (e a b : A) (ea : RelationStar A R e a) (eb : RelationStar A S e b), RelationJoin A (RelationStar A S) (RelationStar A R) a b",
        r"fun (A : Type) (R S : A -> A -> Type)
 (sc : forall (e a b : A), R e a -> S e b -> RelationJoin A (RelationStar A S) R a b)
 (e a b : A) (ea : RelationStar A R e a) (eb : RelationStar A S e b) => @RelationStar.rec A R
  (fun (x y : A) (_ : RelationStar A R x y) =>
   forall (z : A), RelationStar A S x z ->
    RelationJoin A (RelationStar A S) (RelationStar A R) y z)
  (fun (x z : A) (xz : RelationStar A S x z) =>
   @RelationJoin.mk A (RelationStar A S) (RelationStar A R) x z z xz (@RelationStar.refl A R z))
  (fun (x y z : A) (xy : R x y) (_ : RelationStar A R y z)
   (ih : forall (u : A), RelationStar A S y u ->
    RelationJoin A (RelationStar A S) (RelationStar A R) z u)
   (v : A) (xv : RelationStar A S x v) =>
   @RelationJoin.rec A (RelationStar A S) R y v
    (fun (_ : RelationJoin A (RelationStar A S) R y v) =>
     RelationJoin A (RelationStar A S) (RelationStar A R) z v)
    (fun (w : A) (yw : RelationStar A S y w) (vw : R v w) =>
     @RelationJoin.rec A (RelationStar A S) (RelationStar A R) z w
      (fun (_ : RelationJoin A (RelationStar A S) (RelationStar A R) z w) =>
       RelationJoin A (RelationStar A S) (RelationStar A R) z v)
      (fun (q : A) (zq : RelationStar A S z q) (wq : RelationStar A R w q) =>
       @RelationJoin.mk A (RelationStar A S) (RelationStar A R) z v q zq
        (@RelationStar.step A R v w q vw wq)) (ih w yw))
    (relation_strong_commute_strip A R S sc x y v xy xv))
  e a ea b eb",
    ),
    DeclarationInput::Proof(
        "relation_union_confluent",
        r"forall (A : Type) (R S : A -> A -> Type)
 (cr : forall (e a b : A), RelationStar A R e a -> RelationStar A R e b ->
  RelationJoin A (RelationStar A R) (RelationStar A R) a b)
 (cs : forall (e a b : A), RelationStar A S e a -> RelationStar A S e b ->
  RelationJoin A (RelationStar A S) (RelationStar A S) a b)
 (comm : forall (e a b : A), RelationStar A R e a -> RelationStar A S e b ->
  RelationJoin A (RelationStar A S) (RelationStar A R) a b)
 (e a b : A) (ea : RelationStar A (RelationUnion A R S) e a)
 (eb : RelationStar A (RelationUnion A R S) e b), RelationJoin A (RelationStar A (RelationUnion A R S)) (RelationStar A (RelationUnion A R S)) a b",
        r"fun (A : Type) (R S : A -> A -> Type)
 (cr : forall (e a b : A), RelationStar A R e a -> RelationStar A R e b ->
  RelationJoin A (RelationStar A R) (RelationStar A R) a b)
 (cs : forall (e a b : A), RelationStar A S e a -> RelationStar A S e b ->
  RelationJoin A (RelationStar A S) (RelationStar A S) a b)
 (comm : forall (e a b : A), RelationStar A R e a -> RelationStar A S e b ->
  RelationJoin A (RelationStar A S) (RelationStar A R) a b)
 (e a b : A) (ea : RelationStar A (RelationUnion A R S) e a)
 (eb : RelationStar A (RelationUnion A R S) e b) => relation_join_map A
  (RelationStar A (RelationUnion A (RelationStar A R) (RelationStar A S)))
  (RelationStar A (RelationUnion A (RelationStar A R) (RelationStar A S)))
  (RelationStar A (RelationUnion A R S)) (RelationStar A (RelationUnion A R S))
  (relation_macro_to_union A R S) (relation_macro_to_union A R S) a b
  (relation_diamond_confluent A (RelationUnion A (RelationStar A R) (RelationStar A S))
   (relation_union_diamond A (RelationStar A R) (RelationStar A S) cr cs comm)
   e a b (relation_union_to_macro A R S e a ea) (relation_union_to_macro A R S e b eb))",
    ),
    DeclarationInput::Proof(
        "relation_union_confluent_of_strong",
        r"forall (A : Type) (R S : A -> A -> Type)
 (cr : forall (e a b : A), RelationStar A R e a -> RelationStar A R e b ->
  RelationJoin A (RelationStar A R) (RelationStar A R) a b)
 (cs : forall (e a b : A), RelationStar A S e a -> RelationStar A S e b ->
  RelationJoin A (RelationStar A S) (RelationStar A S) a b)
 (sc : forall (e a b : A), R e a -> S e b -> RelationJoin A (RelationStar A S) R a b)
 (e a b : A) (ea : RelationStar A (RelationUnion A R S) e a)
 (eb : RelationStar A (RelationUnion A R S) e b), RelationJoin A (RelationStar A (RelationUnion A R S)) (RelationStar A (RelationUnion A R S)) a b",
        r"fun (A : Type) (R S : A -> A -> Type)
 (cr : forall (e a b : A), RelationStar A R e a -> RelationStar A R e b ->
  RelationJoin A (RelationStar A R) (RelationStar A R) a b)
 (cs : forall (e a b : A), RelationStar A S e a -> RelationStar A S e b ->
  RelationJoin A (RelationStar A S) (RelationStar A S) a b)
 (sc : forall (e a b : A), R e a -> S e b -> RelationJoin A (RelationStar A S) R a b)
 (e a b : A) (ea : RelationStar A (RelationUnion A R S) e a)
 (eb : RelationStar A (RelationUnion A R S) e b) => relation_union_confluent A R S cr cs (relation_strong_commute_star A R S sc) e a b ea eb",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[(
    "forged_relation_join_colors",
    r"forall (A : Type) (R S : A -> A -> Type) (a b : A) (h : RelationJoin A R S a b), RelationJoin A R S b a",
    r"fun (A : Type) (R S : A -> A -> Type) (a b : A) (h : RelationJoin A R S a b) => relation_join_swap A R S a b h",
)];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "relation_star_single",
    "relation_star_trans",
    "relation_star_bind",
    "relation_join_map",
    "relation_join_swap",
    "relation_diamond_strip",
    "relation_diamond_confluent",
    "relation_union_diamond",
    "relation_union_to_macro",
    "relation_macro_to_union",
    "relation_strong_commute_strip",
    "relation_strong_commute_star",
    "relation_union_confluent",
    "relation_union_confluent_of_strong",
];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &["RelationStar", "RelationJoin", "RelationUnion"];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[];

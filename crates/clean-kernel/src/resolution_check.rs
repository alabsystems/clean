// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Computational SAT-resolution refutation checker — *proof by reflection*.
//!
//! # Why this exists (the #20 blocker)
//!
//! [`crate::bitvec_compute`]'s solver-backed bit-blast refutation (width-4
//! commutativity: 28 vars, 131 clauses, 520 resolution steps) cannot be replayed
//! as a *monolithic kernel term*: spelling all 520 resolution steps as nested
//! `Or.rec` makes the kernel eagerly ι/δ-reduce the bit-blast gate trees inside a
//! giant `Or.rec` motive, which OOMs (>70 GB, independently reproduced in
//! [`crate::bitvec_compute`] / the clean-auto Rust replay). The
//! [`clean_auto`-side `replay_resolution_chain`] therefore re-checks the chain in
//! *Rust* — which makes that Rust checker TRUSTED.
//!
//! # The fix (standard SAT/LRAT reflection technique)
//!
//! Instead of a proof *term* whose size is the refutation, we define the
//! resolution checker as a **computational kernel `Definition`** the kernel
//! *evaluates*:
//!
//! ```text
//!   Clean.Res.checkRefutes : List (List Nat) → List Clean.Res.Step → Bool
//! ```
//!
//! over kernel *data* (a literal = `Nat` `2·var + polarity`; a clause = `List
//! Nat`; a step = `Clean.Res.Step.mk resolvent prem1 prem2 pivot`). The proof
//! that a concrete refutation is valid then becomes
//!
//! ```text
//!   Eq.refl Bool Bool.true : checkRefutes <clauses> <refutation> = Bool.true
//! ```
//!
//! whose proof *term* is constant-size (`Eq.refl`); the kernel discharges it by a
//! **linear** ι-reduction over the proof DATA (`List.rec`/`Nat.rec` folds), never
//! building the exponential `Or.rec` tree. This is the SAT-certificate /
//! LRAT-checker reflection pattern (`decide`-style).
//!
//! # What is registered here
//!
//! All reducible `Definition`s (axiom closure ⊆ FOUNDATIONAL_AXIOMS; none are
//! axioms):
//!
//!   * `litBeq`, `litNeg` — literal equality / negation over the `Nat` encoding.
//!   * `clauseMem`, `clauseSubset`, `clauseSeteq` — clause set ops via `List.rec`.
//!   * `resolve` — the *union minus pivot* of two clauses (the raw resolvent
//!     shape). The opposite-polarity side condition and the tautology-free check
//!     are enforced by `checkStep`, NOT by `resolve` (so `resolve` alone is not a
//!     soundness boundary; `checkStep` is).
//!   * `nthClause` — index into the (original ++ derived) clause database.
//!   * `checkStep`, `checkRefutes` — the step / whole-chain validity checker,
//!     mirroring [`replay_resolution_chain`] but as a kernel fold.
//!
//! # Soundness (PROVED — see [`crate::resolution_soundness`])
//!
//! The top-level bridge
//! `checkRefutes_sound : checkRefutes cs pf = true → Unsat cs` is now a kernel
//! `Theorem` (transitive axiom closure ⊆ FOUNDATIONAL_AXIOMS), proved in
//! [`crate::resolution_soundness`] from a real assignment-model semantics
//! (`Holds`/`allSat`/`Unsat` are kernel `Definition`s, not opaque axioms). The
//! genuine resolution-soundness metatheorem is discharged as: `resolveStepSat`
//! (single-step), the membership/append/seteq reflection lemmas, and a fold
//! induction over the refutation list. This required FIXING `resolve` to a SINGLE
//! oriented polarity drop — the previous double-polarity drop `(a∪b) \ {p,¬p}` was
//! actually UNSOUND (it derives the empty clause from the SATISFIABLE set
//! `{(x), (¬x ∨ x)}`). `checkStep` now validates both legal orientations against the
//! oriented resolvent. It is still NOT auto-registered by `init_resolution_check`
//! (that layer is purely computational); run `init_resolution_soundness` to obtain
//! the proved theorem. The exact proved set + axiom closures are reported by the
//! `resolution_soundness` tests.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::name::Name;
use crate::{
    BinderInfo, Constructor, Declaration, EnvError, Environment, Expr, InductiveDecl,
    InductiveType, Level,
};

/// Names of the declarations the resolution-checker layer registers.
pub mod names {
    /// `Clean.Res.Step` — a resolution step `mk resolvent prem1 prem2 pivot`.
    pub const STEP: &str = "Clean.Res.Step";
    /// Constructor `Clean.Res.Step.mk`.
    pub const STEP_MK: &str = "Clean.Res.Step.mk";
    /// `Clean.Res.litBeq : Nat → Nat → Bool` (literal equality).
    pub const LIT_BEQ: &str = "Clean.Res.litBeq";
    /// `Clean.Res.litNeg : Nat → Nat` (flip the polarity bit of a literal).
    pub const LIT_NEG: &str = "Clean.Res.litNeg";
    /// `Clean.Res.clauseMem : Nat → List Nat → Bool`.
    pub const CLAUSE_MEM: &str = "Clean.Res.clauseMem";
    /// `Clause subset: Clean.Res.clauseSubset : List Nat → List Nat → Bool`.
    pub const CLAUSE_SUBSET: &str = "Clean.Res.clauseSubset";
    /// `Clean.Res.clauseSeteq : List Nat → List Nat → Bool` (set-equality).
    pub const CLAUSE_SETEQ: &str = "Clean.Res.clauseSeteq";
    /// `Clean.Res.dropLit : Nat → List Nat → List Nat` (filter out a literal).
    pub const DROP_LIT: &str = "Clean.Res.dropLit";
    /// `Clean.Res.append : List Nat → List Nat → List Nat`.
    pub const APPEND: &str = "Clean.Res.append";
    /// `Clean.Res.resolve : List Nat → List Nat → Nat → List Nat`.
    pub const RESOLVE: &str = "Clean.Res.resolve";
    /// `Clean.Res.nth : List (List Nat) → Nat → List Nat`.
    pub const NTH: &str = "Clean.Res.nth";
    /// `Clean.Res.clauseTautFree : List Nat → Bool` (no literal with its negation).
    pub const CLAUSE_TAUT_FREE: &str = "Clean.Res.clauseTautFree";
    /// `Clean.Res.checkStep : List (List Nat) → Clean.Res.Step → Bool`.
    pub const CHECK_STEP: &str = "Clean.Res.checkStep";
    /// `Clean.Res.checkRefutes : List (List Nat) → List Clean.Res.Step → Bool`.
    pub const CHECK_REFUTES: &str = "Clean.Res.checkRefutes";
    /// `Clean.Res.listLen : List (List Nat) → Nat` (length of the clause DB).
    /// Used by the db-free / newest-first `checkRefutes2` reformulation.
    pub const LIST_LEN: &str = "Clean.Res.listLen";
    /// `Clean.Res.clauseOf2 : List(List Nat) → List(List Nat) → Nat → Nat → List Nat`
    /// — db-free, newest-first premise lookup `(cs, derived, count, j)`. See
    /// `register_check2`. PERFORMANCE reformulation; soundness proved separately.
    pub const CLAUSE_OF2: &str = "Clean.Res.clauseOf2";
    /// `Clean.Res.checkStep2 : List(List Nat) → List(List Nat) → Nat → Step → Bool`
    /// — single-step validity against the db-free newest-first clause store
    /// `(cs, derived, count, s)`.
    pub const CHECK_STEP2: &str = "Clean.Res.checkStep2";
    /// `Clean.Res.checkRefutes2 : List (List Nat) → List Clean.Res.Step → Bool`
    /// — db-free, newest-first reformulation of `checkRefutes` (no growing DB / no
    /// `snocStep`). PERFORMANCE only; its soundness theorem is a SEPARATE task.
    pub const CHECK_REFUTES2: &str = "Clean.Res.checkRefutes2";
    /// `Clean.Res.Holds : Nat → Prop` — the literal-truth model. As of #22 this is
    /// an explicit `Nat → Prop` PARAMETER throughout the soundness proof (no longer a
    /// global opaque axiom); the name is retained for reference.
    pub const HOLDS: &str = "Clean.Res.Holds";
    /// `Clean.Res.Unsat : List (List Nat) → Prop` — now a real model `Definition`
    /// registered by `Environment::register_semantics` (was an opaque axiom).
    pub const UNSAT: &str = "Clean.Res.Unsat";
    /// PROVED: `Clean.Res.emptyClauseUnsat : checkRefutes ... last-empty bridge`.
    pub const EMPTY_CLAUSE_UNSAT: &str = "Clean.Res.emptyClauseUnsat";
    /// PROVED (#22) `Clean.Res.checkRefutes_sound` — the soundness bridge, now a
    /// kernel `Theorem` (closure ⊆ FOUNDATIONAL) via `init_resolution_soundness`.
    pub const CHECK_REFUTES_SOUND: &str = "Clean.Res.checkRefutes_sound";

    // ── §6c sub-quadratic trie checker (checkRefutes3) ─────────────────────────
    /// `Clean.Res.Trie` — a Nat-indexed binary radix trie over clause ids.
    /// `inductive Trie | leaf | node (val : List Nat) (lo hi : Trie)`.
    pub const TRIE: &str = "Clean.Res.Trie";
    /// Constructor `Clean.Res.Trie.leaf`.
    pub const TRIE_LEAF: &str = "Clean.Res.Trie.leaf";
    /// Constructor `Clean.Res.Trie.node`.
    pub const TRIE_NODE: &str = "Clean.Res.Trie.node";
    /// `Clean.Res.trieGet : Trie → Nat → List Nat` — O(log key) descent on the
    /// TRIE (`Trie.rec`), one native `key/2`+`key%2` per level. Absent ⇒ `nil`.
    pub const TRIE_GET: &str = "Clean.Res.trieGet";
    /// `Clean.Res.trieIns : Trie → Nat → List Nat → Trie` — path-copy insert,
    /// O(log key) by the bits of the (literal) key.
    pub const TRIE_INS: &str = "Clean.Res.trieIns";
    /// `Clean.Res.checkStep3 : Trie → Clean.Res.Step → Bool` — single-step
    /// validity with both premise lookups served by `trieGet` (no bound / lenCs).
    pub const CHECK_STEP3: &str = "Clean.Res.checkStep3";
    /// `Clean.Res.checkRefutes3 : Trie → List Clean.Res.Step → Bool` — the
    /// trie-backed fold (db is a `Trie` keyed on global clause id). PERFORMANCE
    /// checker; PROVED sound via `Clean.Res.checkRefutes3_sound`.
    pub const CHECK_REFUTES3: &str = "Clean.Res.checkRefutes3";
    /// `Clean.Res.initialTrie : List (List Nat) → Trie` — the kernel DEFINITION
    /// `initialTrieGo cs Trie.leaf 0` (clause `cs[i]` inserted at global id `i`).
    /// This is the EXACT initial-trie form in `checkRefutes3_sound`'s hypothesis
    /// (registered by `register_initial_trie_all_sat` in `resolution_soundness`),
    /// so a reflection cert built with `initialTrie cs`/`listLen cs` matches that
    /// theorem's hypothesis syntactically. (Distinct from [`encode_initial_trie`],
    /// which pre-builds the SAME trie value by nested `trieIns` at encode time.)
    pub const INITIAL_TRIE: &str = "Clean.Res.initialTrie";
}

// ── small Expr helpers ────────────────────────────────────────────────────────

fn nat_ty() -> Expr {
    Expr::const_str("Nat")
}
fn bool_ty() -> Expr {
    Expr::const_str("Bool")
}
fn btrue() -> Expr {
    Expr::const_str("Bool.true")
}
fn bfalse() -> Expr {
    Expr::const_str("Bool.false")
}
fn band(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.and"), [x, y])
}
fn bor(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.or"), [x, y])
}
fn nat_beq(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.beq"), [x, y])
}
/// `List Nat`.
fn list_nat() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        nat_ty(),
    )
}
/// `List (List Nat)`.
fn list_list_nat() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        list_nat(),
    )
}
/// `List Clean.Res.Step`.
fn list_step() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        Expr::const_str(names::STEP),
    )
}
/// `@List.nil.{0} α`.
fn list_nil(elem: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        elem,
    )
}
/// `@List.cons.{0} α h t`.
fn list_cons(elem: Expr, h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
        [elem, h, t],
    )
}
/// `@List.rec.{1,0} α (motive := fun _ => <result_ty>) nil_case cons_case major`.
/// `result_ty` is a *closed* (non-dependent) result type.
fn list_rec(elem: Expr, result_ty: Expr, nil_case: Expr, cons_case: Expr, major: Expr) -> Expr {
    // List.rec.{u_motive, u_elem}; here motive lives in Sort (succ 0) for Bool/List
    // results — use level (succ zero) for the motive universe, zero for the elem.
    let rec = Expr::const_(
        Name::from_string("List.rec"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );
    let motive = Expr::lam(BinderInfo::Default, list_ty_of(&elem), result_ty);
    Expr::apps(rec, [elem, motive, nil_case, cons_case, major])
}
/// `List α` for the given element type expression.
fn list_ty_of(elem: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        elem.clone(),
    )
}

/// Nat literal `n` as `Nat.succ^n Nat.zero` (UNARY — O(n) to reduce arithmetic).
/// Used by the original `checkRefutes`/`checkRefutes2` id encoding.
fn nat_lit(n: u64) -> Expr {
    let mut e = Expr::const_str("Nat.zero");
    for _ in 0..n {
        e = Expr::app(Expr::const_str("Nat.succ"), e);
    }
    e
}

/// Nat literal `n` as a BigNat LITERAL (`Expr::nat_lit` / `Literal::Nat`). Native
/// `Nat.add/sub/div/mod/ble` reduce on this in O(1)/O(log) — the whole point of the
/// sub-quadratic trie (`checkRefutes3`). Used by the literal-id encoders.
fn lit_nat(n: u64) -> Expr {
    Expr::nat_lit(n)
}

/// `Clean.Res.Trie`.
fn trie_ty() -> Expr {
    Expr::const_str(names::TRIE)
}

impl Environment {
    /// Register the computational resolution-checker layer (reflection backend)
    /// plus the staged soundness lemmas.
    ///
    /// Idempotent. Requires `Bool`, `Nat`, `List`, `Eq`, `Nat.beq`; initializes
    /// them if absent. The checker ops are reducible `Definition`s with axiom
    /// closure ⊆ FOUNDATIONAL_AXIOMS.
    ///
    /// # Errors
    /// Propagates any [`EnvError`] from declaration insertion / kernel checking.
    pub fn init_resolution_check(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::CHECK_REFUTES))
            .is_some()
        {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_nat()?;
        self.init_list()?;
        self.init_nat_cmp()?; // Nat.beq
        self.init_bv_compute()?; // litClash / Bool helpers for soundness lemmas

        self.register_step_inductive()?;
        self.register_lit_ops()?;
        self.register_clause_ops()?;
        self.register_resolve()?;
        self.register_nth()?;
        self.register_check()?;
        self.register_check2()?;
        self.register_check3()?;
        self.register_soundness_lemmas()?;
        Ok(())
    }

    // ── §1 the Step inductive ─────────────────────────────────────────────────

    fn register_step_inductive(&mut self) -> Result<(), EnvError> {
        if self
            .get_inductive(&Name::from_string(names::STEP))
            .is_some()
        {
            return Ok(());
        }
        // inductive Clean.Res.Step where
        //   | mk (resolvent : List Nat) (prem1 prem2 pivot : Nat) : Clean.Res.Step
        let step_ty = Expr::type_();
        let mk_ty = {
            let mut b = EnvDeclBuilder::new();
            let (rid, _) = b.fresh_local(list_nat());
            let (p1, _) = b.fresh_local(nat_ty());
            let (p2, _) = b.fresh_local(nat_ty());
            let (pv, _) = b.fresh_local(nat_ty());
            let r = Expr::const_str(names::STEP);
            let r = b.mk_pi(pv, BinderInfo::Default, nat_ty(), r);
            let r = b.mk_pi(p2, BinderInfo::Default, nat_ty(), r);
            let r = b.mk_pi(p1, BinderInfo::Default, nat_ty(), r);
            let r = b.mk_pi(rid, BinderInfo::Default, list_nat(), r);
            b.finish(r)
        };
        self.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(names::STEP),
                type_: step_ty,
                constructors: vec![Constructor {
                    name: Name::from_string(names::STEP_MK),
                    type_: mk_ty,
                }],
            }],
        })
    }

    // ── §2 literal ops ────────────────────────────────────────────────────────

    fn register_lit_ops(&mut self) -> Result<(), EnvError> {
        // litBeq a b := Nat.beq a b
        let beq_ty = Expr::arrow(nat_ty(), Expr::arrow(nat_ty(), bool_ty()));
        let beq_val = {
            let mut b = EnvDeclBuilder::new();
            let (xid, x) = b.fresh_local(nat_ty());
            let (yid, y) = b.fresh_local(nat_ty());
            let body = nat_beq(x, y);
            let e = b.mk_lam(yid, BinderInfo::Default, nat_ty(), body);
            b.finish(b.mk_lam(xid, BinderInfo::Default, nat_ty(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::LIT_BEQ),
            level_params: vec![],
            type_: beq_ty,
            value: beq_val,
            is_reducible: true,
        })?;

        // litNeg l := Bool.rec-free polarity flip:
        //   if l is even (positive var v=l/2) -> l+1 ; if odd -> l-1.
        // Encode as: Nat.rec base on (Nat.beq (l % 2) 0) is awkward; instead use the
        // closed form  litNeg l := Nat.rec (succ 0) (fun p _ => <flip on parity>) — but
        // parity needs its own recursion. Simpler reducible def: litNeg l :=
        //   (Nat.rec (motive := fun _ => Nat) Nat.zero (fun p ih => ...) l) is parity.
        // We use the direct two-step "xor 1" on the low bit via Nat.rec depth-2:
        //   litNeg 0 = 1, litNeg 1 = 0, litNeg (succ (succ n)) = succ (succ (litNeg n)).
        // = add 2*(l/2) to (1 - l%2). Implement with a helper `parityFlip`.
        let neg_ty = Expr::arrow(nat_ty(), nat_ty());
        let neg_val = self.lit_neg_value();
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::LIT_NEG),
            level_params: vec![],
            type_: neg_ty,
            value: neg_val,
            is_reducible: true,
        })?;
        Ok(())
    }

    /// `litNeg l` flips literal polarity: `0↔1, 2↔3, 4↔5, …`.
    ///
    /// Built by `Nat.rec` with a two-deep pattern via an auxiliary inductive on the
    /// recursion: `litNeg = Nat.rec (succ 0) step l` where `step p ih` must yield
    /// `litNeg (succ p)`. Since `litNeg (succ p) = ` (if p even → p, else p+2…), the
    /// clean closed form is `litNeg l = 2*(l/2) + (1 - l%2)`. We instead use the
    /// elementary recursion `litNeg (succ (succ n)) = succ (succ (litNeg n))` realized
    /// with course-of-values via `Nat.rec` returning a *pair* `(litNeg n, litNeg (succ n))`,
    /// projected. Encoded with `Prod`-free pairing through a `Nat → Nat → Nat` carrier.
    ///
    /// NOTE: this `Nat.rec` recursion is LOAD-BEARING for SYMBOLIC reduction — the
    /// lemma `Clean.Res.halfOddLitNeg` (bool_model.rs, used by the encoding-fidelity
    /// bridge) is proved by reduction relying on the definitional equation
    /// `litNeg (succ (succ n)) = succ (succ (litNeg n))` on a SYMBOLIC `n`. A native
    /// `Nat.div`/`Nat.mod` closed form would only reduce on literals, breaking that
    /// proof; do NOT swap it without re-proving `halfOddLitNeg`. (litNeg is NOT the
    /// `checkRefutes3` bottleneck anyway — that is whnf-cache thrashing on the growing
    /// trie, addressed in `bv_blast_reflection::reflection_cache_budget`.)
    fn lit_neg_value(&self) -> Expr {
        // Carrier: fun (l) => (Nat.rec
        //    (motive := fun _ => Nat → Nat → Nat)   -- continuation (cur, nxt) => result
        //    (fun k => k succ0? ...)
        // This is intricate; use the simplest correct recursion:
        //   litNeg l = Nat.rec (Nat.succ Nat.zero)             -- litNeg 0 = 1
        //                       (fun p ih => <litNeg (succ p)>) l
        // with the step computing litNeg(succ p) from a SECOND parallel recursion that
        // tracks parity. To avoid Prod we recurse to a function `Nat → Nat`:
        //   g : Nat → (Bool → Nat)  where g l false = litNeg l, g l true = litNeg (succ l)
        // g 0      = fun b => Bool.rec 1 0 b            -- litNeg 0 =1, litNeg 1 =0
        // g (succ p) = fun b => Bool.rec (g p true) (succ (succ (g p false))) b
        //   (litNeg (succ p) = g p true; litNeg (succ (succ p)) = succ (succ (litNeg p)))
        let nat = nat_ty();
        let bool_t = bool_ty();
        let g_carrier = Expr::arrow(bool_t.clone(), nat.clone()); // Bool → Nat
        let nat_rec = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        );
        // The inner Bool.rec returns `Nat` (Sort 1), so its motive universe is succ 0.
        let bool_rec = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
        // motive : fun (_ : Nat) => Bool → Nat
        let motive = Expr::lam(BinderInfo::Default, nat.clone(), g_carrier.clone());
        // zero case : fun (b : Bool) => Bool.rec (motive:=fun _=>Nat) 1 0 b
        let zero_case = {
            let inner_motive = Expr::lam(BinderInfo::Default, bool_t.clone(), nat.clone());
            let body = Expr::apps(
                bool_rec.clone(),
                [inner_motive, nat_lit(1), nat_lit(0), Expr::bvar(0)],
            );
            Expr::lam(BinderInfo::Default, bool_t.clone(), body)
        };
        // succ case : fun (p : Nat) (ih : Bool → Nat) (b : Bool) =>
        //   Bool.rec (ih true) (succ (succ (ih false))) b
        let succ_case = {
            // bvars: b=0, ih=1, p=2
            let ih = Expr::bvar(1);
            let inner_motive = Expr::lam(BinderInfo::Default, bool_t.clone(), nat.clone());
            let ih_true = Expr::app(ih.clone(), btrue());
            let ss_ih_false = Expr::app(
                Expr::const_str("Nat.succ"),
                Expr::app(Expr::const_str("Nat.succ"), Expr::app(ih, bfalse())),
            );
            let body = Expr::apps(
                bool_rec.clone(),
                [inner_motive, ih_true, ss_ih_false, Expr::bvar(0)],
            );
            // fun p ih b => body
            Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    g_carrier.clone(),
                    Expr::lam(BinderInfo::Default, bool_t.clone(), body),
                ),
            )
        };
        // litNeg l := Nat.rec motive zero_case succ_case l false
        let mut b = EnvDeclBuilder::new();
        let (lid, l) = b.fresh_local(nat.clone());
        let g = Expr::apps(nat_rec, [motive, zero_case, succ_case, l]);
        let body = Expr::app(g, bfalse());
        b.finish(b.mk_lam(lid, BinderInfo::Default, nat, body))
    }

    // ── §3 clause set ops (List Nat folds) ────────────────────────────────────

    fn register_clause_ops(&mut self) -> Result<(), EnvError> {
        // clauseMem x c := List.rec false (fun h _ ih => Bool.or (litBeq x h) ih) c
        let mem_ty = Expr::arrow(nat_ty(), Expr::arrow(list_nat(), bool_ty()));
        let mem_val = {
            let mut b = EnvDeclBuilder::new();
            let (xid, x) = b.fresh_local(nat_ty());
            let (cid, c) = b.fresh_local(list_nat());
            // cons case: fun (h : Nat) (t : List Nat) (ih : Bool) =>
            //   Bool.or (litBeq x h) ih
            let cons_case = {
                let or = |p: Expr, q: Expr| Expr::apps(Expr::const_str("Bool.or"), [p, q]);
                let lit_beq =
                    Expr::apps(Expr::const_str(names::LIT_BEQ), [x.clone(), Expr::bvar(2)]);
                let body = or(lit_beq, Expr::bvar(0));
                Expr::lam(
                    BinderInfo::Default,
                    nat_ty(),
                    Expr::lam(
                        BinderInfo::Default,
                        list_nat(),
                        Expr::lam(BinderInfo::Default, bool_ty(), body),
                    ),
                )
            };
            let body = list_rec(nat_ty(), bool_ty(), bfalse(), cons_case, c);
            let e = b.mk_lam(cid, BinderInfo::Default, list_nat(), body);
            b.finish(b.mk_lam(xid, BinderInfo::Default, nat_ty(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::CLAUSE_MEM),
            level_params: vec![],
            type_: mem_ty,
            value: mem_val,
            is_reducible: true,
        })?;

        // clauseSubset a b := List.rec true (fun h _ ih => Bool.and (clauseMem h b) ih) a
        let sub_ty = Expr::arrow(list_nat(), Expr::arrow(list_nat(), bool_ty()));
        let sub_val = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(list_nat());
            let (bid2, bb) = b.fresh_local(list_nat());
            let cons_case = {
                let mem = Expr::apps(
                    Expr::const_str(names::CLAUSE_MEM),
                    [Expr::bvar(2), bb.clone()],
                );
                let body = band(mem, Expr::bvar(0));
                Expr::lam(
                    BinderInfo::Default,
                    nat_ty(),
                    Expr::lam(
                        BinderInfo::Default,
                        list_nat(),
                        Expr::lam(BinderInfo::Default, bool_ty(), body),
                    ),
                )
            };
            let body = list_rec(nat_ty(), bool_ty(), btrue(), cons_case, a);
            let e = b.mk_lam(bid2, BinderInfo::Default, list_nat(), body);
            b.finish(b.mk_lam(aid, BinderInfo::Default, list_nat(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::CLAUSE_SUBSET),
            level_params: vec![],
            type_: sub_ty.clone(),
            value: sub_val,
            is_reducible: true,
        })?;

        // clauseSeteq a b := Bool.and (clauseSubset a b) (clauseSubset b a)
        let seteq_val = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(list_nat());
            let (bid2, bb) = b.fresh_local(list_nat());
            let ab = Expr::apps(
                Expr::const_str(names::CLAUSE_SUBSET),
                [a.clone(), bb.clone()],
            );
            let ba = Expr::apps(
                Expr::const_str(names::CLAUSE_SUBSET),
                [bb.clone(), a.clone()],
            );
            let body = band(ab, ba);
            let e = b.mk_lam(bid2, BinderInfo::Default, list_nat(), body);
            b.finish(b.mk_lam(aid, BinderInfo::Default, list_nat(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::CLAUSE_SETEQ),
            level_params: vec![],
            type_: sub_ty,
            value: seteq_val,
            is_reducible: true,
        })?;

        // dropLit x c := List.rec nil (fun h t ih =>
        //   Bool.rec (cons h ih) ih (litBeq x h)) c   -- keep h unless h == x
        let drop_ty = Expr::arrow(nat_ty(), Expr::arrow(list_nat(), list_nat()));
        let drop_val = {
            let mut b = EnvDeclBuilder::new();
            let (xid, x) = b.fresh_local(nat_ty());
            let (cid, c) = b.fresh_local(list_nat());
            let cons_case = {
                // bvars: ih=0, t=1, h=2 ; x is free (xid)
                let h = Expr::bvar(2);
                let ih = Expr::bvar(0);
                let keep = list_cons(nat_ty(), h.clone(), ih.clone());
                let lit_beq = Expr::apps(Expr::const_str(names::LIT_BEQ), [x.clone(), h]);
                // Bool.rec (motive:=fun _ => List Nat) keep ih lit_beq
                //   false → keep (not equal) ; true → drop (ih)
                let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), list_nat());
                let body = Expr::apps(
                    Expr::const_(
                        Name::from_string("Bool.rec"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [inner_motive, keep, ih, lit_beq],
                );
                Expr::lam(
                    BinderInfo::Default,
                    nat_ty(),
                    Expr::lam(
                        BinderInfo::Default,
                        list_nat(),
                        Expr::lam(BinderInfo::Default, list_nat(), body),
                    ),
                )
            };
            let body = list_rec(nat_ty(), list_nat(), list_nil(nat_ty()), cons_case, c);
            let e = b.mk_lam(cid, BinderInfo::Default, list_nat(), body);
            b.finish(b.mk_lam(xid, BinderInfo::Default, nat_ty(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::DROP_LIT),
            level_params: vec![],
            type_: drop_ty,
            value: drop_val,
            is_reducible: true,
        })?;

        // append a b := List.rec b (fun h _ ih => cons h ih) a
        let app_ty = Expr::arrow(list_nat(), Expr::arrow(list_nat(), list_nat()));
        let app_val = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(list_nat());
            let (bid2, bb) = b.fresh_local(list_nat());
            let cons_case = {
                let h = Expr::bvar(2);
                let ih = Expr::bvar(0);
                let body = list_cons(nat_ty(), h, ih);
                Expr::lam(
                    BinderInfo::Default,
                    nat_ty(),
                    Expr::lam(
                        BinderInfo::Default,
                        list_nat(),
                        Expr::lam(BinderInfo::Default, list_nat(), body),
                    ),
                )
            };
            let body = list_rec(nat_ty(), list_nat(), bb.clone(), cons_case, a);
            let e = b.mk_lam(bid2, BinderInfo::Default, list_nat(), body);
            b.finish(b.mk_lam(aid, BinderInfo::Default, list_nat(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::APPEND),
            level_params: vec![],
            type_: app_ty,
            value: app_val,
            is_reducible: true,
        })?;

        // clauseTautFree c := List.rec true
        //   (fun h _ ih => Bool.and (Bool.not (clauseMem (litNeg h) c)) ih) c
        // — true iff NO literal of `c` has its negation also present in `c`. This
        // rejects tautological resolvents (the kernel mirror of the Rust `resolve`'s
        // tautology check). `c` is the outer free var, referenced inside the fold.
        let taut_ty = Expr::arrow(list_nat(), bool_ty());
        let taut_val = {
            let mut b = EnvDeclBuilder::new();
            let (cid, c) = b.fresh_local(list_nat());
            let cons_case = {
                // bvars: ih=0, t=1, h=2 ; c is the free fvar
                let h = Expr::bvar(2);
                let neg_h = Expr::app(Expr::const_str(names::LIT_NEG), h);
                let mem = Expr::apps(Expr::const_str(names::CLAUSE_MEM), [neg_h, c.clone()]);
                let not_mem = Expr::app(Expr::const_str("Bool.not"), mem);
                let body = band(not_mem, Expr::bvar(0));
                Expr::lam(
                    BinderInfo::Default,
                    nat_ty(),
                    Expr::lam(
                        BinderInfo::Default,
                        list_nat(),
                        Expr::lam(BinderInfo::Default, bool_ty(), body),
                    ),
                )
            };
            let body = list_rec(nat_ty(), bool_ty(), btrue(), cons_case, c);
            b.finish(b.mk_lam(cid, BinderInfo::Default, list_nat(), body))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::CLAUSE_TAUT_FREE),
            level_params: vec![],
            type_: taut_ty,
            value: taut_val,
            is_reducible: true,
        })
    }

    // ── §4 resolve ────────────────────────────────────────────────────────────

    fn register_resolve(&mut self) -> Result<(), EnvError> {
        // resolve a b pivot := append (dropLit pivot a) (dropLit (litNeg pivot) b)
        //
        // ORIENTED, SINGLE-polarity drop: remove the *positive* pivot literal from
        // `a` and the *negative* pivot literal from `b`. This is the soundness-
        // critical shape: the earlier double-polarity drop `(a∪b) \ {p,¬p}` is
        // UNSOUND — e.g. from the SATISFIABLE set `a={p}`, `b={¬p,p}` it strips both
        // copies and derives `∅`. The single oriented drop keeps the *true*-polarity
        // pivot copy, so the resolvent stays a logical consequence of `a ∧ b` (the
        // resolution rule). `checkStep` picks the orientation by the side condition.
        let ty = Expr::arrow(
            list_nat(),
            Expr::arrow(list_nat(), Expr::arrow(nat_ty(), list_nat())),
        );
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (aid, a) = b.fresh_local(list_nat());
            let (bid2, bb) = b.fresh_local(list_nat());
            let (pid, p) = b.fresh_local(nat_ty());
            let neg_p = Expr::app(Expr::const_str(names::LIT_NEG), p.clone());
            let drop = |x: Expr, c: Expr| Expr::apps(Expr::const_str(names::DROP_LIT), [x, c]);
            // drop p from a, drop ¬p from b (single, oriented).
            let a1 = drop(p.clone(), a.clone());
            let b1 = drop(neg_p, bb.clone());
            let body = Expr::apps(Expr::const_str(names::APPEND), [a1, b1]);
            let e = b.mk_lam(pid, BinderInfo::Default, nat_ty(), body);
            let e = b.mk_lam(bid2, BinderInfo::Default, list_nat(), e);
            b.finish(b.mk_lam(aid, BinderInfo::Default, list_nat(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::RESOLVE),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    // ── §5 nth (clause-DB index) ──────────────────────────────────────────────

    fn register_nth(&mut self) -> Result<(), EnvError> {
        // nth db i := List.rec (fun _ => nil)
        //                       (fun h _ ih => Nat.rec (fun _ => List Nat) h (fun k _ => ih k) ...) ...
        // Simpler: nth db i := (List.rec
        //    (motive := fun _ => Nat → List Nat)
        //    (fun _ => nil)
        //    (fun h t ihf => fun i => Nat.rec h (fun k _ => ihf k) i)
        //    db) i
        let ty = Expr::arrow(list_list_nat(), Expr::arrow(nat_ty(), list_nat()));
        let nat_to_list = Expr::arrow(nat_ty(), list_nat());
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (dbid, db) = b.fresh_local(list_list_nat());
            let (iid, i) = b.fresh_local(nat_ty());
            // nil case : fun (_ : Nat) => nil
            let nil_case = Expr::lam(BinderInfo::Default, nat_ty(), list_nil(nat_ty()));
            // cons case : fun (h : List Nat) (t : List (List Nat)) (ihf : Nat → List Nat) =>
            //   fun (i : Nat) => Nat.rec (motive := fun _ => List Nat) h (fun k _ => ihf k) i
            let cons_case = {
                // bvars under the outer cons lambdas: i=0, ihf=1, t=2, h=3
                let h = Expr::bvar(3);
                let inner_motive = Expr::lam(BinderInfo::Default, nat_ty(), list_nat());
                // succ case of Nat.rec: fun (k : Nat) (_ : List Nat) => ihf k
                // Inside these two extra lambdas, `ihf` (outer bvar 1) is bvar 3, k is bvar 1.
                let nat_succ_case = Expr::lam(
                    BinderInfo::Default,
                    nat_ty(),
                    Expr::lam(
                        BinderInfo::Default,
                        list_nat(),
                        Expr::app(Expr::bvar(3), Expr::bvar(1)),
                    ),
                );
                let nat_rec = Expr::const_(
                    Name::from_string("Nat.rec"),
                    vec![Level::succ(Level::zero())],
                );
                let inner = Expr::apps(nat_rec, [inner_motive, h, nat_succ_case, Expr::bvar(0)]);
                // fun h t ihf i => inner
                Expr::lam(
                    BinderInfo::Default,
                    list_nat(),
                    Expr::lam(
                        BinderInfo::Default,
                        list_list_nat(),
                        Expr::lam(
                            BinderInfo::Default,
                            nat_to_list.clone(),
                            Expr::lam(BinderInfo::Default, nat_ty(), inner),
                        ),
                    ),
                )
            };
            // List.rec with motive (fun _ => Nat → List Nat)
            let rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(Level::zero()), Level::zero()],
            );
            let motive = Expr::lam(BinderInfo::Default, list_list_nat(), nat_to_list.clone());
            let folded = Expr::apps(rec, [list_nat(), motive, nil_case, cons_case, db]);
            let body = Expr::app(folded, i);
            let e = b.mk_lam(iid, BinderInfo::Default, nat_ty(), body);
            b.finish(b.mk_lam(dbid, BinderInfo::Default, list_list_nat(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::NTH),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    // ── §6 checkStep / checkRefutes ───────────────────────────────────────────

    fn register_check(&mut self) -> Result<(), EnvError> {
        // checkStep db s := Clean.Res.Step.rec
        //   (fun resolvent prem1 prem2 pivot =>
        //      clauseSeteq resolvent (resolve (nth db prem1) (nth db prem2) pivot)) s
        let cs_ty = Expr::arrow(
            list_list_nat(),
            Expr::arrow(Expr::const_str(names::STEP), bool_ty()),
        );
        let cs_val = {
            let mut b = EnvDeclBuilder::new();
            let (dbid, db) = b.fresh_local(list_list_nat());
            let (sid, s) = b.fresh_local(Expr::const_str(names::STEP));
            // Step.rec (motive := fun _ => Bool) mk_case s
            let step_rec = Expr::const_(
                Name::from_string("Clean.Res.Step.rec"),
                vec![Level::succ(Level::zero())],
            );
            let motive = Expr::lam(BinderInfo::Default, Expr::const_str(names::STEP), bool_ty());
            // mk_case : fun (resolvent : List Nat) (prem1 prem2 pivot : Nat) => ...
            let mk_case = {
                // bvars: pivot=0, prem2=1, prem1=2, resolvent=3
                let resolvent = Expr::bvar(3);
                let prem1 = Expr::bvar(2);
                let prem2 = Expr::bvar(1);
                // The recorded pivot is the POSITIVE literal of the pivot var
                // (`encode_step` pins it via `encode_lit(pivot_var, false)`).
                let pivot_pos = Expr::bvar(0);
                let pivot_neg = Expr::app(Expr::const_str(names::LIT_NEG), pivot_pos.clone());
                let nth = |i: Expr| Expr::apps(Expr::const_str(names::NTH), [db.clone(), i]);
                let a = nth(prem1);
                let b_clause = nth(prem2);
                let mem = |x: Expr, c: Expr| Expr::apps(Expr::const_str(names::CLAUSE_MEM), [x, c]);
                let seteq = |rec: Expr, comp: Expr| {
                    Expr::apps(Expr::const_str(names::CLAUSE_SETEQ), [rec, comp])
                };
                let resolve = |x: Expr, y: Expr| {
                    Expr::apps(Expr::const_str(names::RESOLVE), [x, y, pivot_pos.clone()])
                };
                // ORIENTATION-AWARE resolution side condition + resolvent shape. The
                // oriented `resolve x y p = dropLit p x ++ dropLit ¬p y` is sound only
                // when `p∈x` and `¬p∈y`. checkStep validates BOTH legal orientations:
                //   A : (pos∈a ∧ neg∈b) — recorded ≟ resolve a b   (drop p from a, ¬p from b)
                //   B : (neg∈a ∧ pos∈b) — recorded ≟ resolve b a   (drop p from b, ¬p from a)
                let pos_in_a = mem(pivot_pos.clone(), a.clone());
                let neg_in_a = mem(pivot_neg.clone(), a.clone());
                let pos_in_b = mem(pivot_pos.clone(), b_clause.clone());
                let neg_in_b = mem(pivot_neg, b_clause.clone());
                // branch A: orientation (p∈a ∧ ¬p∈b) AND recorded ≟ resolve a b p
                let branch_a = band(
                    band(pos_in_a, neg_in_b),
                    seteq(resolvent.clone(), resolve(a.clone(), b_clause.clone())),
                );
                // branch B: orientation (¬p∈a ∧ p∈b) AND recorded ≟ resolve b a p
                let branch_b = band(
                    band(neg_in_a, pos_in_b),
                    seteq(resolvent.clone(), resolve(b_clause, a)),
                );
                let oriented = bor(branch_a, branch_b);
                // the resolvent must additionally be TAUTOLOGY-FREE (no literal clashing
                // with its own negation), mirroring the Rust `resolve` tautology check.
                let taut_free = Expr::app(Expr::const_str(names::CLAUSE_TAUT_FREE), resolvent);
                let body = band(oriented, taut_free);
                Expr::lam(
                    BinderInfo::Default,
                    list_nat(),
                    Expr::lam(
                        BinderInfo::Default,
                        nat_ty(),
                        Expr::lam(
                            BinderInfo::Default,
                            nat_ty(),
                            Expr::lam(BinderInfo::Default, nat_ty(), body),
                        ),
                    ),
                )
            };
            let body = Expr::apps(step_rec, [motive, mk_case, s]);
            let e = b.mk_lam(sid, BinderInfo::Default, Expr::const_str(names::STEP), body);
            b.finish(b.mk_lam(dbid, BinderInfo::Default, list_list_nat(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::CHECK_STEP),
            level_params: vec![],
            type_: cs_ty,
            value: cs_val,
            is_reducible: true,
        })?;

        self.register_check_refutes()
    }

    /// `checkRefutes db steps`: fold the step list, threading the growing DB
    /// (`db ++ recorded resolvents`), `Bool.and`-ing each `checkStep`, and finally
    /// asserting the last recorded clause is empty.
    fn register_check_refutes(&mut self) -> Result<(), EnvError> {
        // We implement with a helper structure inline via List.rec over steps,
        // carrying `(db, lastEmpty, ok)`. To avoid Prod, fold to a function
        //   Nat-free carrier: List Step → (List (List Nat) → Bool)
        // where the argument is the current DB; result is "all steps from here ok AND
        // ends empty". Concretely:
        //   go : List Step → List (List Nat) → Bool
        //   go nil db := false                         -- a refutation must have ≥1 step
        //   go (cons s rest) db :=
        //       Bool.and (checkStep db s)
        //         (Bool.rec (lastIsEmpty s) (go rest (append-step db s)) (isNil rest))
        // where on the LAST step we additionally require its recorded clause empty.
        //
        // Encoded: go := List.rec (motive := fun _ => List(List Nat) → Bool)
        //   (fun _ => false)
        //   (fun s rest ih => fun db =>
        //       Bool.and (checkStep db s)
        //         (Bool.rec
        //            /-rest = nil-/ (stepResolventEmpty s)
        //            /-rest = cons-/ (ih (snocStep db s))
        //            (listIsCons rest)))
        //   steps db0
        // Helpers needed: stepResolventEmpty, snocStep (append the step's recorded
        // clause to db), listIsCons (Bool on whether a List Step is cons).
        self.register_step_helpers()?;

        let cr_ty = Expr::arrow(list_list_nat(), Expr::arrow(list_step(), bool_ty()));
        let db_to_bool = Expr::arrow(list_list_nat(), bool_ty());
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (dbid, db0) = b.fresh_local(list_list_nat());
            let (stepsid, steps) = b.fresh_local(list_step());

            // nil case : fun (_ : List(List Nat)) => false
            let nil_case = Expr::lam(BinderInfo::Default, list_list_nat(), bfalse());
            // cons case : fun (s : Step) (rest : List Step) (ih : ...) => fun (db) => ...
            let cons_case = {
                // bvars (top to bottom): db=0, ih=1, rest=2, s=3
                let s = Expr::bvar(3);
                let rest = Expr::bvar(2);
                let ih = Expr::bvar(1);
                let db = Expr::bvar(0);
                let check_step =
                    Expr::apps(Expr::const_str(names::CHECK_STEP), [db.clone(), s.clone()]);
                let step_empty = Expr::app(Expr::const_str(STEP_RESOLVENT_EMPTY), s.clone());
                let snoc = Expr::apps(Expr::const_str(SNOC_STEP), [db.clone(), s.clone()]);
                let go_rest = Expr::app(ih, snoc);
                let is_cons = Expr::app(Expr::const_str(LIST_STEP_IS_CONS), rest);
                let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), bool_ty());
                // Bool.rec (motive := fun _ => Bool) step_empty go_rest is_cons
                //   false → rest is nil → require resolvent empty
                //   true  → rest is cons → recurse
                let tail = Expr::apps(
                    Expr::const_(
                        Name::from_string("Bool.rec"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [inner_motive, step_empty, go_rest, is_cons],
                );
                let body = band(check_step, tail);
                // fun s rest ih db => body
                Expr::lam(
                    BinderInfo::Default,
                    Expr::const_str(names::STEP),
                    Expr::lam(
                        BinderInfo::Default,
                        list_step(),
                        Expr::lam(
                            BinderInfo::Default,
                            db_to_bool.clone(),
                            Expr::lam(BinderInfo::Default, list_list_nat(), body),
                        ),
                    ),
                )
            };
            // List.rec over steps with motive (fun _ => List(List Nat) → Bool)
            let rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(Level::zero()), Level::zero()],
            );
            let motive = Expr::lam(BinderInfo::Default, list_step(), db_to_bool.clone());
            let folded = Expr::apps(
                rec,
                [
                    Expr::const_str(names::STEP),
                    motive,
                    nil_case,
                    cons_case,
                    steps,
                ],
            );
            let body = Expr::app(folded, db0);
            let e = b.mk_lam(stepsid, BinderInfo::Default, list_step(), body);
            b.finish(b.mk_lam(dbid, BinderInfo::Default, list_list_nat(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::CHECK_REFUTES),
            level_params: vec![],
            type_: cr_ty,
            value: val,
            is_reducible: true,
        })
    }

    /// Register `stepResolventEmpty`, `snocStep`, `listStepIsCons` helpers.
    fn register_step_helpers(&mut self) -> Result<(), EnvError> {
        // stepResolventEmpty s := Step.rec (fun resolvent _ _ _ => listIsNil resolvent) s
        //   listIsNil c := List.rec true (fun _ _ _ => false) c
        let list_is_nil = {
            let mut b = EnvDeclBuilder::new();
            let (cid, c) = b.fresh_local(list_nat());
            let cons_case = Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                Expr::lam(
                    BinderInfo::Default,
                    list_nat(),
                    Expr::lam(BinderInfo::Default, bool_ty(), bfalse()),
                ),
            );
            let body = list_rec(nat_ty(), bool_ty(), btrue(), cons_case, c);
            b.finish(b.mk_lam(cid, BinderInfo::Default, list_nat(), body))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(LIST_IS_NIL),
            level_params: vec![],
            type_: Expr::arrow(list_nat(), bool_ty()),
            value: list_is_nil,
            is_reducible: true,
        })?;

        let step_empty = {
            let mut b = EnvDeclBuilder::new();
            let (sid, s) = b.fresh_local(Expr::const_str(names::STEP));
            let step_rec = Expr::const_(
                Name::from_string("Clean.Res.Step.rec"),
                vec![Level::succ(Level::zero())],
            );
            let motive = Expr::lam(BinderInfo::Default, Expr::const_str(names::STEP), bool_ty());
            // mk_case: fun resolvent prem1 prem2 pivot => listIsNil resolvent
            let mk_case = Expr::lam(
                BinderInfo::Default,
                list_nat(),
                Expr::lam(
                    BinderInfo::Default,
                    nat_ty(),
                    Expr::lam(
                        BinderInfo::Default,
                        nat_ty(),
                        Expr::lam(
                            BinderInfo::Default,
                            nat_ty(),
                            Expr::app(Expr::const_str(LIST_IS_NIL), Expr::bvar(3)),
                        ),
                    ),
                ),
            );
            let body = Expr::apps(step_rec, [motive, mk_case, s]);
            b.finish(b.mk_lam(sid, BinderInfo::Default, Expr::const_str(names::STEP), body))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(STEP_RESOLVENT_EMPTY),
            level_params: vec![],
            type_: Expr::arrow(Expr::const_str(names::STEP), bool_ty()),
            value: step_empty,
            is_reducible: true,
        })?;

        // snocStep db s := append-at-end: db ++ [resolvent s].
        //   We realize append-of-singleton by a List.rec that rebuilds db then conses
        //   the new clause at the nil tail.
        // stepResolvent s := Step.rec (fun resolvent _ _ _ => resolvent) s
        let step_resolvent = {
            let mut b = EnvDeclBuilder::new();
            let (sid, s) = b.fresh_local(Expr::const_str(names::STEP));
            let step_rec = Expr::const_(
                Name::from_string("Clean.Res.Step.rec"),
                vec![Level::succ(Level::zero())],
            );
            let motive = Expr::lam(
                BinderInfo::Default,
                Expr::const_str(names::STEP),
                list_nat(),
            );
            let mk_case = Expr::lam(
                BinderInfo::Default,
                list_nat(),
                Expr::lam(
                    BinderInfo::Default,
                    nat_ty(),
                    Expr::lam(
                        BinderInfo::Default,
                        nat_ty(),
                        Expr::lam(BinderInfo::Default, nat_ty(), Expr::bvar(3)),
                    ),
                ),
            );
            let body = Expr::apps(step_rec, [motive, mk_case, s]);
            b.finish(b.mk_lam(sid, BinderInfo::Default, Expr::const_str(names::STEP), body))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(STEP_RESOLVENT),
            level_params: vec![],
            type_: Expr::arrow(Expr::const_str(names::STEP), list_nat()),
            value: step_resolvent,
            is_reducible: true,
        })?;

        // snocStep db s := List.rec (cons (stepResolvent s) nil) (fun h _ ih => cons h ih) db
        let snoc = {
            let mut b = EnvDeclBuilder::new();
            let (dbid, db) = b.fresh_local(list_list_nat());
            let (sid, s) = b.fresh_local(Expr::const_str(names::STEP));
            let resolvent = Expr::app(Expr::const_str(STEP_RESOLVENT), s.clone());
            let base = list_cons(list_nat(), resolvent, list_nil(list_nat()));
            // cons case: fun (h : List Nat) (t : List(List Nat)) (ih : List(List Nat)) => cons h ih
            let cons_case = Expr::lam(
                BinderInfo::Default,
                list_nat(),
                Expr::lam(
                    BinderInfo::Default,
                    list_list_nat(),
                    Expr::lam(
                        BinderInfo::Default,
                        list_list_nat(),
                        list_cons(list_nat(), Expr::bvar(2), Expr::bvar(0)),
                    ),
                ),
            );
            // List.rec over db : element type = List Nat
            let rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(Level::zero()), Level::zero()],
            );
            let motive = Expr::lam(BinderInfo::Default, list_list_nat(), list_list_nat());
            let body = Expr::apps(rec, [list_nat(), motive, base, cons_case, db]);
            let e = b.mk_lam(sid, BinderInfo::Default, Expr::const_str(names::STEP), body);
            b.finish(b.mk_lam(dbid, BinderInfo::Default, list_list_nat(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(SNOC_STEP),
            level_params: vec![],
            type_: Expr::arrow(
                list_list_nat(),
                Expr::arrow(Expr::const_str(names::STEP), list_list_nat()),
            ),
            value: snoc,
            is_reducible: true,
        })?;

        // listStepIsCons l := List.rec false (fun _ _ _ => true) l
        let is_cons = {
            let mut b = EnvDeclBuilder::new();
            let (lid, l) = b.fresh_local(list_step());
            let cons_case = Expr::lam(
                BinderInfo::Default,
                Expr::const_str(names::STEP),
                Expr::lam(
                    BinderInfo::Default,
                    list_step(),
                    Expr::lam(BinderInfo::Default, bool_ty(), btrue()),
                ),
            );
            let rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(Level::zero()), Level::zero()],
            );
            let motive = Expr::lam(BinderInfo::Default, list_step(), bool_ty());
            let body = Expr::apps(
                rec,
                [Expr::const_str(names::STEP), motive, bfalse(), cons_case, l],
            );
            b.finish(b.mk_lam(lid, BinderInfo::Default, list_step(), body))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(LIST_STEP_IS_CONS),
            level_params: vec![],
            type_: Expr::arrow(list_step(), bool_ty()),
            value: is_cons,
            is_reducible: true,
        })
    }

    // ── §6b checkRefutes2 — db-free, newest-first reformulation ────────────────
    //
    // PERFORMANCE reformulation of `checkRefutes` (design
    // `designs/2026-06-19-checkrefutes-subquadratic.md`). It kills both O(steps²)
    // sources of the original: (1) the growing-DB `snocStep` append per step, and
    // (2) the positional `nth db j` lookup. Instead of threading a growing
    // `db = cs ++ recorded-resolvents`, it carries only the recorded resolvents,
    // stored NEWEST-FIRST in `derived`, plus a `count : Nat` of how many derived so
    // far. A premise id `j` resolves to a clause in two FIXED lists:
    //
    //   clauseOf2 cs derived count j :=
    //     if j < |cs|  then  nth cs j                                   -- original
    //     else               nth derived (count - 1 - (j - |cs|))       -- derived, newest-first
    //
    // (derived clause with id |cs|+k sits at recency index count-1-k; for the
    // current step's premises k = j-|cs|). On CDCL refutations the cited derived
    // clauses are RECENT (small recency index) → typically O(1) per lookup.
    //
    // SOUNDNESS-CRITICAL INVARIANT: `checkStep2` additionally requires each premise
    // `p < |cs| + count` (the `boundOk` check). Without it the TRUNCATED `Nat.sub`
    // (floored at 0) would alias an out-of-range derived premise to recency index 0
    // = the MOST-RECENT derived clause, fabricating a spurious justification. The
    // bound check rejects any such forged premise BEFORE the aliasing can matter.
    //
    // This is purely the COMPUTATIONAL reformulation gated by the smoke test
    // (`checkRefutes2` must reduce identically to `checkRefutes`); its soundness
    // theorem is a separate task and is NOT registered here. The proven O(steps²)
    // `checkRefutes` + `checkRefutes_sound` remain the trust root.
    fn register_check2(&mut self) -> Result<(), EnvError> {
        // ── SUB-QUADRATIC listLen (2026-06-20 fix) ──
        // The old `listLen db := List.rec Nat.zero (fun _ _ ih => Nat.succ ih) db`
        // reduces to a UNARY succ-chain `Nat.succ^|cs| Nat.zero`. When that unary
        // value seeds `checkRefutes3`'s `nextId`, every threaded `Nat.succ nextId`
        // stays unary and each `trieIns acc nextId c` extracts key bits via
        // `Nat.div`/`Nat.mod`, which only reduce NATIVELY on BigNat LITERALS — so a
        // unary id makes each insert O(id), the whole step-insert phase O(steps²).
        //
        // FIX: a tail/accumulator fold seeded at the BigNat LITERAL 0. `Nat.succ`
        // on a BigNat literal reduces NATIVELY to the next literal
        // (`tc/reduction/nat.rs`), so `listLenAux cs (lit 0)` whnf's to the LITERAL
        // `|cs|`. Then `checkRefutes3 (initialTrie cs) (listLen cs)`'s nextId is a
        // literal and stays a literal under every `Nat.succ` → each step insert is
        // O(log id) → fully sub-quadratic. (Same value as before; only the REDUCED
        // FORM changes from unary to BigNat literal.)
        //
        // listLenAux db acc := List.rec (fun acc => acc)
        //                               (fun _ _ ih => fun acc => ih (Nat.succ acc)) db acc
        // listLen db := listLenAux db 0   (0 = BigNat literal).
        let nat_to_nat = Expr::arrow(nat_ty(), nat_ty());
        let aux_val = {
            let mut b = EnvDeclBuilder::new();
            let (dbid, db) = b.fresh_local(list_list_nat());
            let (accid, acc) = b.fresh_local(nat_ty());
            // nil case : fun (acc : Nat) => acc
            let nil_case = Expr::lam(BinderInfo::Default, nat_ty(), Expr::bvar(0));
            // cons case : fun (h : List Nat) (t : List(List Nat)) (ih : Nat → Nat) =>
            //   fun (acc : Nat) => ih (Nat.succ acc)
            //   bvars under the acc lambda: acc=0, ih=1, t=2, h=3
            let cons_case = Expr::lam(
                BinderInfo::Default,
                list_nat(),
                Expr::lam(
                    BinderInfo::Default,
                    list_list_nat(),
                    Expr::lam(
                        BinderInfo::Default,
                        nat_to_nat.clone(),
                        Expr::lam(
                            BinderInfo::Default,
                            nat_ty(),
                            Expr::app(
                                Expr::bvar(1),
                                Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0)),
                            ),
                        ),
                    ),
                ),
            );
            // List.rec over element type `List Nat`, result `Nat → Nat`.
            let rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(Level::zero()), Level::zero()],
            );
            let motive = Expr::lam(BinderInfo::Default, list_list_nat(), nat_to_nat.clone());
            let folded = Expr::apps(rec, [list_nat(), motive, nil_case, cons_case, db]);
            let body = Expr::app(folded, acc);
            let e = b.mk_lam(accid, BinderInfo::Default, nat_ty(), body);
            b.finish(b.mk_lam(dbid, BinderInfo::Default, list_list_nat(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(LIST_LEN_AUX),
            level_params: vec![],
            type_: Expr::arrow(list_list_nat(), nat_to_nat),
            value: aux_val,
            is_reducible: true,
        })?;

        // listLen db := listLenAux db 0   (start acc = BigNat literal 0).
        let len_val = {
            let mut b = EnvDeclBuilder::new();
            let (dbid, db) = b.fresh_local(list_list_nat());
            let body = Expr::apps(Expr::const_str(LIST_LEN_AUX), [db, lit_nat(0)]);
            b.finish(b.mk_lam(dbid, BinderInfo::Default, list_list_nat(), body))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::LIST_LEN),
            level_params: vec![],
            type_: Expr::arrow(list_list_nat(), nat_ty()),
            value: len_val,
            is_reducible: true,
        })?;

        self.register_clause_of2()?;
        self.register_check_step2()?;
        self.register_check_refutes2()
    }

    /// `clauseOf2 cs derived count j` — db-free, newest-first premise lookup.
    fn register_clause_of2(&mut self) -> Result<(), EnvError> {
        let nat_succ = |e: Expr| Expr::app(Expr::const_str("Nat.succ"), e);
        let nat_sub = |x: Expr, y: Expr| Expr::apps(Expr::const_str("Nat.sub"), [x, y]);
        let nat_ble = |x: Expr, y: Expr| Expr::apps(Expr::const_str("Nat.ble"), [x, y]);
        let nth = |db: Expr, i: Expr| Expr::apps(Expr::const_str(names::NTH), [db, i]);
        let list_len = |db: Expr| Expr::app(Expr::const_str(names::LIST_LEN), db);

        let ty = Expr::arrow(
            list_list_nat(),
            Expr::arrow(
                list_list_nat(),
                Expr::arrow(nat_ty(), Expr::arrow(nat_ty(), list_nat())),
            ),
        );
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (csid, cs) = b.fresh_local(list_list_nat());
            let (derid, derived) = b.fresh_local(list_list_nat());
            let (cntid, count) = b.fresh_local(nat_ty());
            let (jid, j) = b.fresh_local(nat_ty());
            let len_cs = list_len(cs.clone());
            // CS-branch (true: j < |cs|): nth cs j.
            let cs_branch = nth(cs.clone(), j.clone());
            // DERIVED-branch (false: j >= |cs|):
            //   nth derived ((count - 1) - (j - |cs|)).
            let recency = nat_sub(
                nat_sub(count.clone(), nat_succ(Expr::const_str("Nat.zero"))),
                nat_sub(j.clone(), len_cs.clone()),
            );
            let der_branch = nth(derived.clone(), recency);
            // scrutinee: Nat.ble (succ j) |cs|  ≡  (j < |cs|).
            let scrut = nat_ble(nat_succ(j.clone()), len_cs);
            // Bool.rec (motive := fun _ => List Nat) <false=DERIVED> <true=CS> scrut.
            let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), list_nat());
            let body = Expr::apps(
                Expr::const_(
                    Name::from_string("Bool.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [inner_motive, der_branch, cs_branch, scrut],
            );
            let e = b.mk_lam(jid, BinderInfo::Default, nat_ty(), body);
            let e = b.mk_lam(cntid, BinderInfo::Default, nat_ty(), e);
            let e = b.mk_lam(derid, BinderInfo::Default, list_list_nat(), e);
            b.finish(b.mk_lam(csid, BinderInfo::Default, list_list_nat(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::CLAUSE_OF2),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    /// `checkStep2 cs derived count s` — single-step validity, db-free.
    ///
    /// Mirrors `checkStep`'s `mk_case` EXACTLY (the two-orientation oriented-resolve
    /// side condition + `clauseTautFree`), with `nth db premK` replaced by
    /// `clauseOf2 cs derived count premK`, AND guarded by `boundOk prem1 ∧ boundOk
    /// prem2` where `boundOk p = Nat.ble (succ p) (|cs| + count)` (i.e. `p < |cs| +
    /// count`). The bound check is the soundness boundary for the truncated-Nat.sub
    /// recency arithmetic (see `register_check2` header).
    fn register_check_step2(&mut self) -> Result<(), EnvError> {
        let nat_succ = |e: Expr| Expr::app(Expr::const_str("Nat.succ"), e);
        let nat_add = |x: Expr, y: Expr| Expr::apps(Expr::const_str("Nat.add"), [x, y]);
        let nat_ble = |x: Expr, y: Expr| Expr::apps(Expr::const_str("Nat.ble"), [x, y]);
        let list_len = |db: Expr| Expr::app(Expr::const_str(names::LIST_LEN), db);

        let ty = Expr::arrow(
            list_list_nat(),
            Expr::arrow(
                list_list_nat(),
                Expr::arrow(
                    nat_ty(),
                    Expr::arrow(Expr::const_str(names::STEP), bool_ty()),
                ),
            ),
        );
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (csid, cs) = b.fresh_local(list_list_nat());
            let (derid, derived) = b.fresh_local(list_list_nat());
            let (cntid, count) = b.fresh_local(nat_ty());
            let (sid, s) = b.fresh_local(Expr::const_str(names::STEP));
            // upper bound for a valid premise id: |cs| + count.
            let limit = nat_add(list_len(cs.clone()), count.clone());

            let step_rec = Expr::const_(
                Name::from_string("Clean.Res.Step.rec"),
                vec![Level::succ(Level::zero())],
            );
            let motive = Expr::lam(BinderInfo::Default, Expr::const_str(names::STEP), bool_ty());
            // mk_case : fun (resolvent : List Nat) (prem1 prem2 pivot : Nat) => ...
            let mk_case = {
                // bvars: pivot=0, prem2=1, prem1=2, resolvent=3
                let resolvent = Expr::bvar(3);
                let prem1 = Expr::bvar(2);
                let prem2 = Expr::bvar(1);
                let pivot_pos = Expr::bvar(0);
                let pivot_neg = Expr::app(Expr::const_str(names::LIT_NEG), pivot_pos.clone());
                // db-free premise lookup.
                let clause_of = |id: Expr| {
                    Expr::apps(
                        Expr::const_str(names::CLAUSE_OF2),
                        [cs.clone(), derived.clone(), count.clone(), id],
                    )
                };
                let a = clause_of(prem1.clone());
                let b_clause = clause_of(prem2.clone());
                let mem = |x: Expr, c: Expr| Expr::apps(Expr::const_str(names::CLAUSE_MEM), [x, c]);
                let seteq = |rec: Expr, comp: Expr| {
                    Expr::apps(Expr::const_str(names::CLAUSE_SETEQ), [rec, comp])
                };
                let resolve = |x: Expr, y: Expr| {
                    Expr::apps(Expr::const_str(names::RESOLVE), [x, y, pivot_pos.clone()])
                };
                // SOUNDNESS GUARD: each premise id must be < |cs| + count, else the
                // truncated Nat.sub recency aliases an out-of-range derived premise to
                // index 0 (most-recent), which is unsound.
                let bound_ok = |p: Expr| nat_ble(nat_succ(p), limit.clone());
                let bounds = band(bound_ok(prem1), bound_ok(prem2));
                // ORIENTATION-AWARE resolution side condition (identical to checkStep).
                let pos_in_a = mem(pivot_pos.clone(), a.clone());
                let neg_in_a = mem(pivot_neg.clone(), a.clone());
                let pos_in_b = mem(pivot_pos.clone(), b_clause.clone());
                let neg_in_b = mem(pivot_neg, b_clause.clone());
                let branch_a = band(
                    band(pos_in_a, neg_in_b),
                    seteq(resolvent.clone(), resolve(a.clone(), b_clause.clone())),
                );
                let branch_b = band(
                    band(neg_in_a, pos_in_b),
                    seteq(resolvent.clone(), resolve(b_clause, a)),
                );
                let oriented = bor(branch_a, branch_b);
                let taut_free = Expr::app(Expr::const_str(names::CLAUSE_TAUT_FREE), resolvent);
                // checkStep2 = boundOk ∧ (oriented ∧ tautFree).
                let body = band(bounds, band(oriented, taut_free));
                Expr::lam(
                    BinderInfo::Default,
                    list_nat(),
                    Expr::lam(
                        BinderInfo::Default,
                        nat_ty(),
                        Expr::lam(
                            BinderInfo::Default,
                            nat_ty(),
                            Expr::lam(BinderInfo::Default, nat_ty(), body),
                        ),
                    ),
                )
            };
            let body = Expr::apps(step_rec, [motive, mk_case, s]);
            let e = b.mk_lam(sid, BinderInfo::Default, Expr::const_str(names::STEP), body);
            let e = b.mk_lam(cntid, BinderInfo::Default, nat_ty(), e);
            let e = b.mk_lam(derid, BinderInfo::Default, list_list_nat(), e);
            b.finish(b.mk_lam(csid, BinderInfo::Default, list_list_nat(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::CHECK_STEP2),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    /// `checkRefutes2 cs steps` — the db-free, newest-first fold.
    ///
    /// ```text
    ///   checkRefutes2 cs steps :=
    ///     (List.rec (motive := fun _ => List(List Nat) → Nat → Bool)
    ///        (fun _ _ => Bool.false)
    ///        (fun s rest ih => fun derived count =>
    ///           Bool.and (checkStep2 cs derived count s)
    ///             (Bool.rec (stepResolventEmpty s)
    ///                       (ih (List.cons (stepResolvent s) derived) (Nat.succ count))
    ///                       (listStepIsCons rest)))
    ///        steps) List.nil Nat.zero
    /// ```
    ///
    /// `cs` is the OUTER bound var (an `EnvDeclBuilder` fvar), threaded into
    /// `checkStep2`; the accumulator carries `derived` (newest-first) + `count`.
    fn register_check_refutes2(&mut self) -> Result<(), EnvError> {
        // carrier of the fold: List(List Nat) → Nat → Bool   (derived, count).
        let acc_ty = Expr::arrow(list_list_nat(), Expr::arrow(nat_ty(), bool_ty()));
        let cr_ty = Expr::arrow(list_list_nat(), Expr::arrow(list_step(), bool_ty()));
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (csid, cs) = b.fresh_local(list_list_nat());
            let (stepsid, steps) = b.fresh_local(list_step());

            // nil case : fun (_derived : List(List Nat)) (_count : Nat) => Bool.false
            let nil_case = Expr::lam(
                BinderInfo::Default,
                list_list_nat(),
                Expr::lam(BinderInfo::Default, nat_ty(), bfalse()),
            );
            // cons case : fun (s) (rest) (ih) => fun (derived) (count) => body
            let cons_case = {
                // bvars: count=0, derived=1, ih=2, rest=3, s=4 ; cs is an outer fvar.
                let s = Expr::bvar(4);
                let rest = Expr::bvar(3);
                let ih = Expr::bvar(2);
                let derived = Expr::bvar(1);
                let count = Expr::bvar(0);
                let check_step2 = Expr::apps(
                    Expr::const_str(names::CHECK_STEP2),
                    [cs.clone(), derived.clone(), count.clone(), s.clone()],
                );
                let step_empty = Expr::app(Expr::const_str(STEP_RESOLVENT_EMPTY), s.clone());
                // recurse: ih (cons (stepResolvent s) derived) (succ count).
                let resolvent = Expr::app(Expr::const_str(STEP_RESOLVENT), s);
                let new_derived = list_cons(list_nat(), resolvent, derived);
                let new_count = Expr::app(Expr::const_str("Nat.succ"), count);
                let go_rest = Expr::apps(ih, [new_derived, new_count]);
                let is_cons = Expr::app(Expr::const_str(LIST_STEP_IS_CONS), rest);
                let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), bool_ty());
                // Bool.rec (motive := fun _ => Bool) step_empty go_rest is_cons
                //   false → rest is nil → require resolvent empty
                //   true  → rest is cons → recurse
                let tail = Expr::apps(
                    Expr::const_(
                        Name::from_string("Bool.rec"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [inner_motive, step_empty, go_rest, is_cons],
                );
                let body = band(check_step2, tail);
                // fun s rest ih derived count => body
                Expr::lam(
                    BinderInfo::Default,
                    Expr::const_str(names::STEP),
                    Expr::lam(
                        BinderInfo::Default,
                        list_step(),
                        Expr::lam(
                            BinderInfo::Default,
                            acc_ty.clone(),
                            Expr::lam(
                                BinderInfo::Default,
                                list_list_nat(),
                                Expr::lam(BinderInfo::Default, nat_ty(), body),
                            ),
                        ),
                    ),
                )
            };
            // List.rec over steps with motive (fun _ => List(List Nat) → Nat → Bool).
            let rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(Level::zero()), Level::zero()],
            );
            let motive = Expr::lam(BinderInfo::Default, list_step(), acc_ty.clone());
            let folded = Expr::apps(
                rec,
                [
                    Expr::const_str(names::STEP),
                    motive,
                    nil_case,
                    cons_case,
                    steps,
                ],
            );
            // apply the accumulator seeds: derived := List.nil, count := Nat.zero.
            let body = Expr::apps(folded, [list_nil(list_nat()), Expr::const_str("Nat.zero")]);
            let e = b.mk_lam(stepsid, BinderInfo::Default, list_step(), body);
            b.finish(b.mk_lam(csid, BinderInfo::Default, list_list_nat(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::CHECK_REFUTES2),
            level_params: vec![],
            type_: cr_ty,
            value: val,
            is_reducible: true,
        })
    }

    // ── §6c checkRefutes3 — TRUE sub-quadratic Nat-indexed trie ────────────────
    //
    // PERFORMANCE checker (design `designs/2026-06-19-checkrefutes-subquadratic.md`,
    // "Concrete trie encoding"). Registered ALONGSIDE `checkRefutes`/`checkRefutes2`
    // (both stay the trust root; checkRefutes_sound is unchanged). Its soundness
    // theorem is a SEPARATE later task.
    //
    // The two residual O(steps²) costs of `checkRefutes2` are killed by replacing the
    // `List`-based db (positional `nth` = O(index); `listLen` = O(|cs|); UNARY ids =
    // O(value) per Nat op) with a binary radix trie keyed on the BITS of a LITERAL
    // (`Expr::nat_lit`) clause id:
    //
    //   inductive Trie | leaf | node (val : List Nat) (lo hi : Trie)
    //   trieGet db key : descend the TRIE (Trie.rec) — at a node, key=0 ⇒ val, else
    //     Bool.rec (ih_lo (key/2)) (ih_hi (key/2)) (isOdd key) ; absent ⇒ nil.
    //   trieIns db key v : path-copy insert by the bits of key, O(depth).
    //
    // CRITICAL: the descent recurses on the TRIE (Trie.rec, motive `fun _ => Nat →
    // List Nat`), NOT on the Nat key (Nat.rec on the key would be O(key) even for a
    // literal — defeating the literal-id win). Each level does ONE native `key/2` +
    // `key%2` on the BigNat literal (O(1)/O(log)); depth = bit-width of max id =
    // O(log steps). Over `steps` ops: O(steps · log steps) — genuinely sub-quadratic.
    fn register_check3(&mut self) -> Result<(), EnvError> {
        self.register_trie_inductive()?;
        self.register_trie_get()?;
        self.register_trie_ins()?;
        self.register_check_step3()?;
        self.register_check_refutes3()
    }

    /// `inductive Clean.Res.Trie | leaf | node (val : List Nat) (lo hi : Trie)`.
    /// Registered via `add_inductive` (kernel-derived recursor `Trie.rec`).
    fn register_trie_inductive(&mut self) -> Result<(), EnvError> {
        if self
            .get_inductive(&Name::from_string(names::TRIE))
            .is_some()
        {
            return Ok(());
        }
        let trie_self = Expr::const_str(names::TRIE);
        // leaf : Trie
        let leaf_ty = trie_self.clone();
        // node : (val : List Nat) → (lo : Trie) → (hi : Trie) → Trie
        let node_ty = {
            let mut b = EnvDeclBuilder::new();
            let (vid, _) = b.fresh_local(list_nat());
            let (loid, _) = b.fresh_local(trie_self.clone());
            let (hiid, _) = b.fresh_local(trie_self.clone());
            let r = trie_self.clone();
            let r = b.mk_pi(hiid, BinderInfo::Default, trie_self.clone(), r);
            let r = b.mk_pi(loid, BinderInfo::Default, trie_self.clone(), r);
            let r = b.mk_pi(vid, BinderInfo::Default, list_nat(), r);
            b.finish(r)
        };
        self.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(names::TRIE),
                type_: Expr::type_(),
                constructors: vec![
                    Constructor {
                        name: Name::from_string(names::TRIE_LEAF),
                        type_: leaf_ty,
                    },
                    Constructor {
                        name: Name::from_string(names::TRIE_NODE),
                        type_: node_ty,
                    },
                ],
            }],
        })
    }

    /// `trieGet : Trie → Nat → List Nat` — descend the TRIE by recursing on
    /// `Trie.rec` (motive `fun _ => Nat → List Nat`), threading `key/2` per level.
    ///
    /// ```text
    ///   trieGet db := Trie.rec (motive := fun _ => Nat → List Nat)
    ///     /-leaf-/ (fun _key => nil)
    ///     /-node-/ (fun val lo hi ih_lo ih_hi => fun key =>
    ///                 Bool.rec                                   -- key = 0 ?
    ///                   /-false: key ≠ 0-/ (Bool.rec (ih_lo (key/2)) (ih_hi (key/2))
    ///                                                 (Nat.ble 1 (key%2)))   -- odd → hi
    ///                   /-true:  key = 0-/  val
    ///                   (Nat.ble key 0))
    ///     db
    /// ```
    ///
    /// Recursion depth = trie depth = O(log max-id); each level does one native
    /// `key/2` and `key%2` on the BigNat-literal key. Recursing on the TRIE (not the
    /// key) keeps it O(log) regardless of the literal key's value.
    fn register_trie_get(&mut self) -> Result<(), EnvError> {
        let nat_to_list = Expr::arrow(nat_ty(), list_nat());
        let nat_div = |x: Expr, y: Expr| Expr::apps(Expr::const_str("Nat.div"), [x, y]);
        let nat_mod = |x: Expr, y: Expr| Expr::apps(Expr::const_str("Nat.mod"), [x, y]);
        let nat_ble = |x: Expr, y: Expr| Expr::apps(Expr::const_str("Nat.ble"), [x, y]);
        let bool_rec_list = |fcase: Expr, tcase: Expr, scrut: Expr| {
            let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), list_nat());
            Expr::apps(
                Expr::const_(
                    Name::from_string("Bool.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [inner_motive, fcase, tcase, scrut],
            )
        };

        let val = {
            let mut b = EnvDeclBuilder::new();
            let (dbid, db) = b.fresh_local(trie_ty());
            // leaf case : fun (_key : Nat) => nil
            let leaf_case = Expr::lam(BinderInfo::Default, nat_ty(), list_nil(nat_ty()));
            // node case : fun (val) (lo) (hi) (ih_lo) (ih_hi) => fun (key) => body
            //   bvars in body: key=0, ih_hi=1, ih_lo=2, hi=3, lo=4, val=5
            let node_case = {
                let val_b = Expr::bvar(5);
                let ih_lo = Expr::bvar(2);
                let ih_hi = Expr::bvar(1);
                let key = Expr::bvar(0);
                let half = nat_div(key.clone(), lit_nat(2));
                let is_odd = nat_ble(lit_nat(1), nat_mod(key.clone(), lit_nat(2)));
                // key ≠ 0 branch: odd → hi(key/2), even → lo(key/2).
                let descend = bool_rec_list(
                    Expr::app(ih_lo, half.clone()),
                    Expr::app(ih_hi, half),
                    is_odd,
                );
                // key = 0 ? true → val ; false → descend. scrut = Nat.ble key 0.
                let is_zero = nat_ble(key, lit_nat(0));
                let body = bool_rec_list(descend, val_b, is_zero);
                // fun val lo hi ih_lo ih_hi key => body
                Expr::lam(
                    BinderInfo::Default,
                    list_nat(), // val
                    Expr::lam(
                        BinderInfo::Default,
                        trie_ty(), // lo
                        Expr::lam(
                            BinderInfo::Default,
                            trie_ty(), // hi
                            Expr::lam(
                                BinderInfo::Default,
                                nat_to_list.clone(), // ih_lo
                                Expr::lam(
                                    BinderInfo::Default,
                                    nat_to_list.clone(), // ih_hi
                                    Expr::lam(BinderInfo::Default, nat_ty(), body),
                                ),
                            ),
                        ),
                    ),
                )
            };
            // Trie.rec (motive := fun _ => Nat → List Nat) leaf_case node_case db
            let trie_rec = Expr::const_(
                Name::from_string("Clean.Res.Trie.rec"),
                vec![Level::succ(Level::zero())],
            );
            let motive = Expr::lam(BinderInfo::Default, trie_ty(), nat_to_list.clone());
            let body = Expr::apps(trie_rec, [motive, leaf_case, node_case, db]);
            b.finish(b.mk_lam(dbid, BinderInfo::Default, trie_ty(), body))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::TRIE_GET),
            level_params: vec![],
            type_: Expr::arrow(trie_ty(), Expr::arrow(nat_ty(), list_nat())),
            value: val,
            is_reducible: true,
        })
    }

    /// One-level trie projections `trieVal/trieLo/trieHi` + the fuel-driven insert
    /// `trieInsAux`, then `trieIns := trieInsAux <FUEL>`.
    ///
    /// `trieIns` is RECURSIVE (descend to a child, insert deeper), but a kernel
    /// `Definition` cannot reference itself. We therefore recurse on a FUEL counter
    /// (a literal Nat = the trie's max bit-depth, `TRIE_FUEL`) via `Nat.rec`, whose
    /// succ-case IH is the deeper insert. FUEL is a CONSTANT (independent of the key
    /// value); the recursion depth is the fuel, and each level does ONE native
    /// `key/2`+`key%2`. So even though `Nat.rec` walks the fuel unary, the fuel is a
    /// fixed `O(log max-id)` constant — the descent stays O(log id), NOT O(key).
    ///
    /// At each fuel level: `key=0` ⇒ overwrite this node's value (keep children);
    /// else case on `key%2` and replace the lo/hi child with `ih child (key/2) v`,
    /// projecting the current node's parts via `trieVal/trieLo/trieHi` (which map a
    /// `leaf` to `nil/leaf/leaf`, so a path extends through absent subtrees).
    fn register_trie_ins(&mut self) -> Result<(), EnvError> {
        let leaf = Expr::const_str(names::TRIE_LEAF);
        let node = |v: Expr, lo: Expr, hi: Expr| {
            Expr::apps(Expr::const_str(names::TRIE_NODE), [v, lo, hi])
        };
        // Trie.rec at a non-recursive result type R: project node parts, leaf → dflt.
        // proj R dflt pick := fun t => Trie.rec (fun _ => R) dflt
        //    (fun val lo hi _ihlo _ihhi => pick val lo hi) t
        let make_proj = |result_ty: Expr, dflt: Expr, pick_body: Expr| -> Expr {
            // pick_body is built with bvars: hi=0? — we pass explicit lambdas here.
            let mut bb = EnvDeclBuilder::new();
            let (tid, t) = bb.fresh_local(trie_ty());
            let trie_rec = Expr::const_(
                Name::from_string("Clean.Res.Trie.rec"),
                vec![Level::succ(Level::zero())],
            );
            let motive = Expr::lam(BinderInfo::Default, trie_ty(), result_ty.clone());
            // node case: fun val lo hi ihlo ihhi => pick_body  (pick_body refers to
            //   bvars val=4, lo=3, hi=2 — we build it that way at the call site).
            // The motive is non-dependent `fun _ => result_ty`, so each IH has type
            // `motive child = result_ty` (NOT `Nat → result_ty`).
            let node_case = Expr::lam(
                BinderInfo::Default,
                list_nat(), // val
                Expr::lam(
                    BinderInfo::Default,
                    trie_ty(), // lo
                    Expr::lam(
                        BinderInfo::Default,
                        trie_ty(), // hi
                        Expr::lam(
                            BinderInfo::Default,
                            result_ty.clone(), // ih_lo : motive lo = result_ty
                            Expr::lam(
                                BinderInfo::Default,
                                result_ty.clone(), // ih_hi : motive hi = result_ty
                                pick_body,
                            ),
                        ),
                    ),
                ),
            );
            let body = Expr::apps(trie_rec, [motive, dflt, node_case, t]);
            bb.finish(bb.mk_lam(tid, BinderInfo::Default, trie_ty(), body))
        };
        // trieVal t : List Nat  (leaf → nil, node val _ _ → val)  [val is bvar 4]
        let trie_val = make_proj(list_nat(), list_nil(nat_ty()), Expr::bvar(4));
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(TRIE_VAL),
            level_params: vec![],
            type_: Expr::arrow(trie_ty(), list_nat()),
            value: trie_val,
            is_reducible: true,
        })?;
        // trieLo t : Trie  (leaf → leaf, node _ lo _ → lo)  [lo is bvar 3]
        let trie_lo = make_proj(trie_ty(), leaf.clone(), Expr::bvar(3));
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(TRIE_LO),
            level_params: vec![],
            type_: Expr::arrow(trie_ty(), trie_ty()),
            value: trie_lo,
            is_reducible: true,
        })?;
        // trieHi t : Trie  (leaf → leaf, node _ _ hi → hi)  [hi is bvar 2]
        let trie_hi = make_proj(trie_ty(), leaf.clone(), Expr::bvar(2));
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(TRIE_HI),
            level_params: vec![],
            type_: Expr::arrow(trie_ty(), trie_ty()),
            value: trie_hi,
            is_reducible: true,
        })?;

        // trieInsAux : Nat(fuel) → Trie → Nat(key) → List Nat → Trie
        //   := Nat.rec (motive := fun _ => Trie → Nat → List Nat → Trie) base step fuel
        let nat_div = |x: Expr, y: Expr| Expr::apps(Expr::const_str("Nat.div"), [x, y]);
        let nat_mod = |x: Expr, y: Expr| Expr::apps(Expr::const_str("Nat.mod"), [x, y]);
        let nat_ble = |x: Expr, y: Expr| Expr::apps(Expr::const_str("Nat.ble"), [x, y]);
        let val_of = |t: Expr| Expr::app(Expr::const_str(TRIE_VAL), t);
        let lo_of = |t: Expr| Expr::app(Expr::const_str(TRIE_LO), t);
        let hi_of = |t: Expr| Expr::app(Expr::const_str(TRIE_HI), t);
        let bool_rec_trie = |fcase: Expr, tcase: Expr, scrut: Expr| {
            let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), trie_ty());
            Expr::apps(
                Expr::const_(
                    Name::from_string("Bool.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [inner_motive, fcase, tcase, scrut],
            )
        };
        // carrier of the Nat.rec fold: Trie → Nat → List Nat → Trie.
        let carrier = Expr::arrow(
            trie_ty(),
            Expr::arrow(nat_ty(), Expr::arrow(list_nat(), trie_ty())),
        );
        // `setHere db v := node v (trieLo db) (trieHi db)`  (overwrite value).
        let set_here = |db: Expr, v: Expr| node(v, lo_of(db.clone()), hi_of(db));

        let aux_val = {
            let mut b = EnvDeclBuilder::new();
            let (fid, fuel) = b.fresh_local(nat_ty());
            // base case (fuel = 0): fun (db) (key) (v) => setHere db v.
            //   bvars: v=0, key=1, db=2
            let base_case = {
                let db = Expr::bvar(2);
                let v = Expr::bvar(0);
                let body = set_here(db, v);
                Expr::lam(
                    BinderInfo::Default,
                    trie_ty(),
                    Expr::lam(
                        BinderInfo::Default,
                        nat_ty(),
                        Expr::lam(BinderInfo::Default, list_nat(), body),
                    ),
                )
            };
            // step case: fun (f : Nat) (ih : carrier) => fun (db) (key) (v) => body
            //   bvars: v=0, key=1, db=2, ih=3, f=4
            let step_case = {
                let ih = Expr::bvar(3);
                let db = Expr::bvar(2);
                let key = Expr::bvar(1);
                let v = Expr::bvar(0);
                let half = nat_div(key.clone(), lit_nat(2));
                let is_odd = nat_ble(lit_nat(1), nat_mod(key.clone(), lit_nat(2)));
                // even: node (val db) (ih (lo db) (key/2) v) (hi db)
                let even = node(
                    val_of(db.clone()),
                    Expr::apps(ih.clone(), [lo_of(db.clone()), half.clone(), v.clone()]),
                    hi_of(db.clone()),
                );
                // odd: node (val db) (lo db) (ih (hi db) (key/2) v)
                let odd = node(
                    val_of(db.clone()),
                    lo_of(db.clone()),
                    Expr::apps(ih, [hi_of(db.clone()), half, v.clone()]),
                );
                let descend = bool_rec_trie(even, odd, is_odd);
                let here = set_here(db, v);
                let is_zero = nat_ble(key, lit_nat(0));
                let body = bool_rec_trie(descend, here, is_zero);
                // fun f ih db key v => body
                Expr::lam(
                    BinderInfo::Default,
                    nat_ty(), // f
                    Expr::lam(
                        BinderInfo::Default,
                        carrier.clone(), // ih
                        Expr::lam(
                            BinderInfo::Default,
                            trie_ty(), // db
                            Expr::lam(
                                BinderInfo::Default,
                                nat_ty(), // key
                                Expr::lam(BinderInfo::Default, list_nat(), body),
                            ),
                        ),
                    ),
                )
            };
            let nat_rec = Expr::const_(
                Name::from_string("Nat.rec"),
                vec![Level::succ(Level::zero())],
            );
            let motive = Expr::lam(BinderInfo::Default, nat_ty(), carrier.clone());
            let body = Expr::apps(nat_rec, [motive, base_case, step_case, fuel]);
            b.finish(b.mk_lam(fid, BinderInfo::Default, nat_ty(), body))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(TRIE_INS_AUX),
            level_params: vec![],
            type_: Expr::arrow(nat_ty(), carrier.clone()),
            value: aux_val,
            is_reducible: true,
        })?;

        // trieIns db key v := trieInsAux <FUEL> db key v   (FUEL = fixed bit-depth).
        let ins_val = {
            let mut b = EnvDeclBuilder::new();
            let (dbid, db) = b.fresh_local(trie_ty());
            let (kid, key) = b.fresh_local(nat_ty());
            let (vid, v) = b.fresh_local(list_nat());
            let body = Expr::apps(
                Expr::const_str(TRIE_INS_AUX),
                [lit_nat(TRIE_FUEL), db, key, v],
            );
            let e = b.mk_lam(vid, BinderInfo::Default, list_nat(), body);
            let e = b.mk_lam(kid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_lam(dbid, BinderInfo::Default, trie_ty(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::TRIE_INS),
            level_params: vec![],
            type_: Expr::arrow(
                trie_ty(),
                Expr::arrow(nat_ty(), Expr::arrow(list_nat(), trie_ty())),
            ),
            value: ins_val,
            is_reducible: true,
        })
    }

    /// `checkStep3 db s` — single-step validity, db is a `Trie` keyed by GLOBAL
    /// clause id. Mirrors `checkStep`'s `mk_case` EXACTLY (the two-orientation
    /// oriented-resolve side condition + `clauseTautFree`), with each premise lookup
    /// served by `trieGet db premK` instead of `nth db premK`. No bound check / no
    /// `lenCs` / no cs-derived split: the trie holds ALL clauses by id, and an absent
    /// id returns `nil`, which fails `clauseSeteq` ⇒ the step is rejected (exactly as
    /// an out-of-range `nth` returns `nil`).
    fn register_check_step3(&mut self) -> Result<(), EnvError> {
        let ty = Expr::arrow(
            trie_ty(),
            Expr::arrow(Expr::const_str(names::STEP), bool_ty()),
        );
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (dbid, db) = b.fresh_local(trie_ty());
            let (sid, s) = b.fresh_local(Expr::const_str(names::STEP));
            let step_rec = Expr::const_(
                Name::from_string("Clean.Res.Step.rec"),
                vec![Level::succ(Level::zero())],
            );
            let motive = Expr::lam(BinderInfo::Default, Expr::const_str(names::STEP), bool_ty());
            // mk_case : fun (resolvent : List Nat) (prem1 prem2 pivot : Nat) => ...
            let mk_case = {
                // bvars: pivot=0, prem2=1, prem1=2, resolvent=3
                let resolvent = Expr::bvar(3);
                let prem1 = Expr::bvar(2);
                let prem2 = Expr::bvar(1);
                let pivot_pos = Expr::bvar(0);
                let pivot_neg = Expr::app(Expr::const_str(names::LIT_NEG), pivot_pos.clone());
                let get = |id: Expr| Expr::apps(Expr::const_str(names::TRIE_GET), [db.clone(), id]);
                let a = get(prem1);
                let b_clause = get(prem2);
                let mem = |x: Expr, c: Expr| Expr::apps(Expr::const_str(names::CLAUSE_MEM), [x, c]);
                let seteq = |rec: Expr, comp: Expr| {
                    Expr::apps(Expr::const_str(names::CLAUSE_SETEQ), [rec, comp])
                };
                let resolve = |x: Expr, y: Expr| {
                    Expr::apps(Expr::const_str(names::RESOLVE), [x, y, pivot_pos.clone()])
                };
                let pos_in_a = mem(pivot_pos.clone(), a.clone());
                let neg_in_a = mem(pivot_neg.clone(), a.clone());
                let pos_in_b = mem(pivot_pos.clone(), b_clause.clone());
                let neg_in_b = mem(pivot_neg, b_clause.clone());
                let branch_a = band(
                    band(pos_in_a, neg_in_b),
                    seteq(resolvent.clone(), resolve(a.clone(), b_clause.clone())),
                );
                let branch_b = band(
                    band(neg_in_a, pos_in_b),
                    seteq(resolvent.clone(), resolve(b_clause, a)),
                );
                let oriented = bor(branch_a, branch_b);
                let taut_free = Expr::app(Expr::const_str(names::CLAUSE_TAUT_FREE), resolvent);
                let body = band(oriented, taut_free);
                Expr::lam(
                    BinderInfo::Default,
                    list_nat(),
                    Expr::lam(
                        BinderInfo::Default,
                        nat_ty(),
                        Expr::lam(
                            BinderInfo::Default,
                            nat_ty(),
                            Expr::lam(BinderInfo::Default, nat_ty(), body),
                        ),
                    ),
                )
            };
            let body = Expr::apps(step_rec, [motive, mk_case, s]);
            let e = b.mk_lam(sid, BinderInfo::Default, Expr::const_str(names::STEP), body);
            b.finish(b.mk_lam(dbid, BinderInfo::Default, trie_ty(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::CHECK_STEP3),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    /// `checkRefutes3 db steps` — the trie-backed fold.
    ///
    /// ```text
    ///   checkRefutes3 db steps :=
    ///     (List.rec (motive := fun _ => Trie → Nat → Bool)
    ///        (fun _ _ => Bool.false)
    ///        (fun s rest ih => fun db nextId =>
    ///           Bool.and (checkStep3 db s)
    ///             (Bool.rec (stepResolventEmpty s)
    ///                       (ih (trieIns db nextId (stepResolvent s)) (Nat.succ nextId))
    ///                       (listStepIsCons rest)))
    ///        steps) db0 nextId0
    /// ```
    ///
    /// The accumulator carries the current `Trie` db (originals + derived resolvents,
    /// keyed by global id) and `nextId : Nat` — the id to insert the NEXT resolvent
    /// at. `db0` (the initial trie of `cs`) and `nextId0 = |cs|` are supplied at the
    /// call site (`check_refutes3_app` builds them in Rust by nested `trieIns`, since
    /// `cs` is known at encode time). `nextId` is a LITERAL Nat (native `succ`).
    fn register_check_refutes3(&mut self) -> Result<(), EnvError> {
        // carrier of the fold: Trie → Nat → Bool   (db, nextId).
        let acc_ty = Expr::arrow(trie_ty(), Expr::arrow(nat_ty(), bool_ty()));
        let cr_ty = Expr::arrow(
            trie_ty(),
            Expr::arrow(nat_ty(), Expr::arrow(list_step(), bool_ty())),
        );
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (db0id, db0) = b.fresh_local(trie_ty());
            let (nid, next0) = b.fresh_local(nat_ty());
            let (stepsid, steps) = b.fresh_local(list_step());

            // nil case : fun (_db : Trie) (_nextId : Nat) => Bool.false
            let nil_case = Expr::lam(
                BinderInfo::Default,
                trie_ty(),
                Expr::lam(BinderInfo::Default, nat_ty(), bfalse()),
            );
            // cons case : fun (s) (rest) (ih) => fun (db) (nextId) => body
            //   bvars: nextId=0, db=1, ih=2, rest=3, s=4
            let cons_case = {
                let s = Expr::bvar(4);
                let rest = Expr::bvar(3);
                let ih = Expr::bvar(2);
                let db = Expr::bvar(1);
                let next_id = Expr::bvar(0);
                let check_step3 =
                    Expr::apps(Expr::const_str(names::CHECK_STEP3), [db.clone(), s.clone()]);
                let step_empty = Expr::app(Expr::const_str(STEP_RESOLVENT_EMPTY), s.clone());
                let resolvent = Expr::app(Expr::const_str(STEP_RESOLVENT), s);
                // insert the recorded resolvent at nextId, bump nextId.
                let new_db = Expr::apps(
                    Expr::const_str(names::TRIE_INS),
                    [db, next_id.clone(), resolvent],
                );
                let new_next = Expr::app(Expr::const_str("Nat.succ"), next_id);
                let go_rest = Expr::apps(ih, [new_db, new_next]);
                let is_cons = Expr::app(Expr::const_str(LIST_STEP_IS_CONS), rest);
                let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), bool_ty());
                let tail = Expr::apps(
                    Expr::const_(
                        Name::from_string("Bool.rec"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [inner_motive, step_empty, go_rest, is_cons],
                );
                let body = band(check_step3, tail);
                // fun s rest ih db nextId => body
                Expr::lam(
                    BinderInfo::Default,
                    Expr::const_str(names::STEP),
                    Expr::lam(
                        BinderInfo::Default,
                        list_step(),
                        Expr::lam(
                            BinderInfo::Default,
                            acc_ty.clone(),
                            Expr::lam(
                                BinderInfo::Default,
                                trie_ty(),
                                Expr::lam(BinderInfo::Default, nat_ty(), body),
                            ),
                        ),
                    ),
                )
            };
            let rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(Level::zero()), Level::zero()],
            );
            let motive = Expr::lam(BinderInfo::Default, list_step(), acc_ty.clone());
            let folded = Expr::apps(
                rec,
                [
                    Expr::const_str(names::STEP),
                    motive,
                    nil_case,
                    cons_case,
                    steps,
                ],
            );
            // apply the seeds: db := db0, nextId := next0.
            let body = Expr::apps(folded, [db0, next0]);
            let e = b.mk_lam(stepsid, BinderInfo::Default, list_step(), body);
            let e = b.mk_lam(nid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_lam(db0id, BinderInfo::Default, trie_ty(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::CHECK_REFUTES3),
            level_params: vec![],
            type_: cr_ty,
            value: val,
            is_reducible: true,
        })
    }

    // ── §7 staged soundness ───────────────────────────────────────────────────

    /// Register the soundness layer:
    ///
    ///   * `Holds : Nat → Prop` — abstract literal truth (an uninterpreted `Prop`
    ///     family; the model bridge ties it to a Boolean assignment elsewhere).
    ///   * `Unsat : List (List Nat) → Prop` — no assignment satisfies all clauses.
    ///   * PROVED `emptyClauseUnsat` — the empty clause is unsatisfiable
    ///     (its disjunction is `False`), the resolution endpoint lemma; axiom
    ///     closure ⊆ FOUNDATIONAL_AXIOMS.
    ///
    /// NOTE: the top-level bridge `checkRefutes_sound` is deliberately NOT
    /// registered here. It is an unproved obligation; auto-registering it as a
    /// global `Axiom` would put a citable, unproved soundness axiom into every
    /// environment (and, before the `resolve` side-condition fix, an actually
    /// *false* one). Callers that want the typed obligation must opt in explicitly
    /// via [`Environment::register_check_refutes_sound_stmt`]; see its doc.
    fn register_soundness_lemmas(&mut self) -> Result<(), EnvError> {
        self.init_true_false()?;
        // NOTE (#22): `Holds` and `Unsat` were previously registered HERE as opaque
        // `Axiom`s (an uninterpreted literal-truth family / clause-DB-unsatisfiability
        // predicate). They are now REAL kernel `Definition`s registered by
        // [`Environment::register_semantics`] in `crate::resolution_soundness`
        // (`Holds` is an explicit `Nat → Prop` parameter throughout; `Unsat cs` is the
        // model-theoretic `∀ Holds, resConsistent → resExclusive → allSat → False`).
        // The opaque axioms are gone — the soundness bridge `checkRefutes_sound` is now
        // a PROVED `Theorem` (closure ⊆ FOUNDATIONAL), not a stated axiom.
        self.register_empty_clause_unsat()?;
        Ok(())
    }

    /// PROVED endpoint lemma: the disjunction of the EMPTY clause is `False`.
    ///
    /// `clauseOr (Holds : Nat → Prop) : List Nat → Prop` is the right-folded `Or` of
    /// each literal's `Holds`; `clauseOr Holds List.nil ≡ False` by ι-reduction. So
    ///
    /// ```text
    ///   emptyClauseUnsat : (Holds : Nat → Prop) → clauseOr Holds List.nil → False
    ///                    := fun Holds h => h
    /// ```
    ///
    /// — the empty clause has NO satisfying literal under ANY assignment `Holds`,
    /// hence ⊢ False from it. This is the "empty clause ⊢ False" key lemma. `Holds`
    /// is an explicit PARAMETER (not the global opaque axiom), so the lemma's axiom
    /// closure is `⊆ FOUNDATIONAL_AXIOMS` (empty domain set).
    fn register_empty_clause_unsat(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::EMPTY_CLAUSE_UNSAT))
            .is_some()
        {
            return Ok(());
        }
        // clauseOr Holds c := List.rec False (fun h _ ih => Or (Holds h) ih) c : Prop
        // (Holds : Nat → Prop is an explicit parameter — keeps the lemma foundational.)
        let clause_or_name = "Clean.Res.clauseOr";
        let holds_ty = Expr::arrow(nat_ty(), Expr::prop());
        if self.get_const(&Name::from_string(clause_or_name)).is_none() {
            let val = {
                let mut b = EnvDeclBuilder::new();
                let (hid, holds) = b.fresh_local(holds_ty.clone());
                let (cid, c) = b.fresh_local(list_nat());
                // cons case: fun (h : Nat) (t : List Nat) (ih : Prop) => Or (holds h) ih
                // (`holds` is the outer fvar; `b.finish` abstracts it wherever it
                // appears, including under these inner `Expr::lam`s.)
                let cons_case = {
                    let holds_h = Expr::app(holds.clone(), Expr::bvar(2));
                    let or = Expr::apps(
                        Expr::const_(Name::from_string("Or"), vec![]),
                        [holds_h, Expr::bvar(0)],
                    );
                    Expr::lam(
                        BinderInfo::Default,
                        nat_ty(),
                        Expr::lam(
                            BinderInfo::Default,
                            list_nat(),
                            Expr::lam(BinderInfo::Default, Expr::prop(), or),
                        ),
                    )
                };
                let rec = Expr::const_(
                    Name::from_string("List.rec"),
                    vec![Level::succ(Level::zero()), Level::zero()],
                );
                let motive = Expr::lam(BinderInfo::Default, list_nat(), Expr::prop());
                let body = Expr::apps(
                    rec,
                    [nat_ty(), motive, Expr::const_str("False"), cons_case, c],
                );
                let e = b.mk_lam(cid, BinderInfo::Default, list_nat(), body);
                b.finish(b.mk_lam(hid, BinderInfo::Default, holds_ty.clone(), e))
            };
            self.add_decl_if_absent(Declaration::Definition {
                name: Name::from_string(clause_or_name),
                level_params: vec![],
                type_: Expr::arrow(holds_ty.clone(), Expr::arrow(list_nat(), Expr::prop())),
                value: val,
                is_reducible: true,
            })?;
        }

        // emptyClauseUnsat : (Holds : Nat → Prop) → clauseOr Holds List.nil → False
        //                  := fun Holds (h : clauseOr Holds nil) => h
        // (clauseOr Holds nil ≡ False by ι-reduction, so the identity is the proof.)
        let nil = list_nil(nat_ty());
        let false_c = Expr::const_str("False");
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (hid, holds) = b.fresh_local(holds_ty.clone());
            let clause_or_nil = Expr::apps(
                Expr::const_str(clause_or_name),
                [holds.clone(), nil.clone()],
            );
            let inner = Expr::arrow(clause_or_nil, false_c.clone());
            b.finish(b.mk_pi(hid, BinderInfo::Default, holds_ty.clone(), inner))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (hpid, holds) = b.fresh_local(holds_ty.clone());
            let clause_or_nil = Expr::apps(Expr::const_str(clause_or_name), [holds, nil]);
            let (hid, h) = b.fresh_local(clause_or_nil.clone());
            let inner = b.mk_lam(hid, BinderInfo::Default, clause_or_nil, h);
            b.finish(b.mk_lam(hpid, BinderInfo::Default, holds_ty, inner))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(names::EMPTY_CLAUSE_UNSAT),
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Register the top-level soundness bridge `checkRefutes_sound`.
    ///
    /// `checkRefutes_sound : (cs : List (List Nat)) → (pf : List Clean.Res.Step) →
    ///    Eq (checkRefutes cs pf) Bool.true → Unsat cs`
    ///
    /// As of #22 this is a PROVED `Declaration::Theorem` (transitive axiom closure ⊆
    /// FOUNDATIONAL_AXIOMS), produced by [`Environment::init_resolution_soundness`]
    /// in [`crate::resolution_soundness`] — NOT the stated axiom it used to be. This
    /// wrapper simply delegates so existing opt-in call sites keep working while now
    /// obtaining the genuine proof (the `resolve` single-polarity-drop soundness fix,
    /// the single-step resolution lemma, and the fold induction).
    ///
    /// # Errors
    /// Propagates any [`EnvError`] from declaration insertion / kernel checking.
    pub fn register_check_refutes_sound_stmt(&mut self) -> Result<(), EnvError> {
        self.init_resolution_soundness()
    }
}

// helper names not in the public `names` module (internal reducible defs)
/// `Clean.Res.listLenAux : List (List Nat) → Nat → Nat` — tail/accumulator fold
/// backing `listLen`; `listLenAux db acc` adds `|db|` to `acc` via `Nat.succ`,
/// keeping a BigNat-literal `acc` a literal (sub-quadratic `checkRefutes3` ids).
const LIST_LEN_AUX: &str = "Clean.Res.listLenAux";
const LIST_IS_NIL: &str = "Clean.Res.listIsNil";
const STEP_RESOLVENT_EMPTY: &str = "Clean.Res.stepResolventEmpty";
const STEP_RESOLVENT: &str = "Clean.Res.stepResolvent";
const SNOC_STEP: &str = "Clean.Res.snocStep";
const LIST_STEP_IS_CONS: &str = "Clean.Res.listStepIsCons";
// trie internals (one-level projections + fuel-driven insert helper).
const TRIE_VAL: &str = "Clean.Res.trieVal";
const TRIE_LO: &str = "Clean.Res.trieLo";
const TRIE_HI: &str = "Clean.Res.trieHi";
const TRIE_INS_AUX: &str = "Clean.Res.trieInsAux";
/// Fixed insert/descent fuel = max trie bit-depth. Clause ids are `< |cs| + steps`;
/// even the deepest e2e widths keep `|cs| + steps` well under `2^60`, so 60 bits of
/// fuel covers every id with margin. The fuel is a CONSTANT (independent of the key
/// value), so `trieInsAux`'s `Nat.rec` descent is O(fuel) = O(log max-id), NOT
/// O(key). (`trieGet` needs no fuel — it recurses on the finite `Trie` structure.)
const TRIE_FUEL: u64 = 60;

// ── public data-builders (used by tests + clean-auto reflection demo) ──────────

/// Encode a literal `(var, neg)` as the kernel `Nat` `2·var + (neg ? 1 : 0)`.
pub fn encode_lit(var: u32, neg: bool) -> Expr {
    nat_lit(u64::from(var) * 2 + u64::from(neg))
}

/// Encode a clause (list of `(var, neg)`) as the kernel `List Nat`.
pub fn encode_clause(lits: &[(u32, bool)]) -> Expr {
    let mut e = list_nil(nat_ty());
    for &(v, n) in lits.iter().rev() {
        e = list_cons(nat_ty(), encode_lit(v, n), e);
    }
    e
}

/// Encode a clause database (list of clauses) as the kernel `List (List Nat)`.
pub fn encode_clauses(clauses: &[Vec<(u32, bool)>]) -> Expr {
    let mut e = list_nil(list_nat());
    for c in clauses.iter().rev() {
        e = list_cons(list_nat(), encode_clause(c), e);
    }
    e
}

/// Encode one resolution step as `Clean.Res.Step.mk resolvent prem1 prem2 pivot`.
pub fn encode_step(resolvent: &[(u32, bool)], prem1: u32, prem2: u32, pivot_var: u32) -> Expr {
    Expr::apps(
        Expr::const_str(names::STEP_MK),
        [
            encode_clause(resolvent),
            nat_lit(u64::from(prem1)),
            nat_lit(u64::from(prem2)),
            // pivot encoded as the POSITIVE literal of the pivot var (resolve drops
            // both polarities of it).
            encode_lit(pivot_var, false),
        ],
    )
}

/// Encode a refutation (list of steps) as the kernel `List Clean.Res.Step`.
pub fn encode_refutation(steps: &[(Vec<(u32, bool)>, u32, u32, u32)]) -> Expr {
    let mut e = list_nil(Expr::const_str(names::STEP));
    for (resolvent, p1, p2, piv) in steps.iter().rev() {
        e = list_cons(
            Expr::const_str(names::STEP),
            encode_step(resolvent, *p1, *p2, *piv),
            e,
        );
    }
    e
}

/// `checkRefutes <clauses> <refutation>` as a kernel `Bool` term (the thing the
/// kernel evaluates by reflection).
pub fn check_refutes_app(clauses: Expr, refutation: Expr) -> Expr {
    Expr::apps(Expr::const_str(names::CHECK_REFUTES), [clauses, refutation])
}

/// `checkRefutes2 <clauses> <refutation>` as a kernel `Bool` term — the db-free,
/// newest-first PERFORMANCE reformulation (must reduce identically to
/// [`check_refutes_app`]; soundness theorem is a separate task).
pub fn check_refutes2_app(clauses: Expr, refutation: Expr) -> Expr {
    Expr::apps(
        Expr::const_str(names::CHECK_REFUTES2),
        [clauses, refutation],
    )
}

// ── literal-id encoders + trie builders for the sub-quadratic checkRefutes3 ────
//
// IDENTICAL data to the unary encoders above, except every `Nat` (clause literals'
// var ids via `encode_lit`, premise ids `prem1`/`prem2`, the pivot literal) is a
// BigNat LITERAL (`Expr::nat_lit`) instead of unary `Nat.succ^n Nat.zero`. The
// kernel then reduces `Nat.div`/`Nat.mod`/`Nat.ble` on ids NATIVELY in O(1)/O(log),
// which is what makes the trie descent O(log id) (`tc/reduction/nat.rs`).

/// Literal-id encoding of a literal `(var, neg)` = the BigNat literal `2·var+neg`.
///
/// The BigNat-literal twin of [`encode_lit`]: a single compact `Literal::Nat` node
/// (`Nat.beq`/`Nat.div`/`Nat.mod` reduce on it natively) rather than the unary
/// `Nat.succ^n Nat.zero` chain. Used by the `checkRefutes3` bridge so the clause DB
/// the encoding-fidelity `allSat H cs` proof is about is bit-for-bit the BigNat `cs`
/// the trie checker reduces.
pub fn encode_lit_lit(var: u32, neg: bool) -> Expr {
    lit_nat(u64::from(var) * 2 + u64::from(neg))
}

/// Literal-id encoding of a clause as `List Nat` (literals are BigNat literals).
/// `pub(crate)` for the LRAT-checker layer ([`crate::lrat_check`]), which shares
/// this exact clause encoding.
pub(crate) fn encode_clause_lit(lits: &[(u32, bool)]) -> Expr {
    let mut e = list_nil(nat_ty());
    for &(v, n) in lits.iter().rev() {
        e = list_cons(nat_ty(), encode_lit_lit(v, n), e);
    }
    e
}

/// Literal-id encoding of a clause database as `List (List Nat)`.
pub fn encode_clauses_lit(clauses: &[Vec<(u32, bool)>]) -> Expr {
    let mut e = list_nil(list_nat());
    for c in clauses.iter().rev() {
        e = list_cons(list_nat(), encode_clause_lit(c), e);
    }
    e
}

/// Literal-id encoding of one step `Clean.Res.Step.mk resolvent prem1 prem2 pivot`,
/// with `prem1`/`prem2`/`pivot` as BigNat literals (so the trie's `prem` lookups
/// reduce natively).
pub fn encode_step_lit(resolvent: &[(u32, bool)], prem1: u32, prem2: u32, pivot_var: u32) -> Expr {
    Expr::apps(
        Expr::const_str(names::STEP_MK),
        [
            encode_clause_lit(resolvent),
            lit_nat(u64::from(prem1)),
            lit_nat(u64::from(prem2)),
            encode_lit_lit(pivot_var, false),
        ],
    )
}

/// Literal-id encoding of a refutation as `List Clean.Res.Step`.
pub fn encode_refutation_lit(steps: &[(Vec<(u32, bool)>, u32, u32, u32)]) -> Expr {
    let mut e = list_nil(Expr::const_str(names::STEP));
    for (resolvent, p1, p2, piv) in steps.iter().rev() {
        e = list_cons(
            Expr::const_str(names::STEP),
            encode_step_lit(resolvent, *p1, *p2, *piv),
            e,
        );
    }
    e
}

/// `Clean.Res.Trie.leaf`.
fn trie_leaf() -> Expr {
    Expr::const_str(names::TRIE_LEAF)
}

/// Build the initial trie holding `clauses[i]` at GLOBAL id `i`, emitted as nested
/// `trieIns` applications (`cs` is known at encode time, so we do not need a kernel
/// fold to build it). Returns `trieIns (… (trieIns leaf 0 c0) …) (n-1) c_{n-1}`.
pub fn encode_initial_trie(clauses: &[Vec<(u32, bool)>]) -> Expr {
    let mut t = trie_leaf();
    for (i, c) in clauses.iter().enumerate() {
        t = Expr::apps(
            Expr::const_str(names::TRIE_INS),
            [t, lit_nat(i as u64), encode_clause_lit(c)],
        );
    }
    t
}

/// `checkRefutes3 <initial-trie-of-clauses> <|clauses|> <steps>` as a kernel `Bool`
/// term — the TRUE sub-quadratic trie checker. `clauses`/`steps` are the SAME
/// data passed to [`check_refutes_app`], but the initial trie is built by nested
/// `trieIns` (ids `0..|clauses|`) and all ids are BigNat literals. Must reduce
/// identically to `checkRefutes` (smoke gate); soundness is a separate task.
pub fn check_refutes3_app(
    clauses: &[Vec<(u32, bool)>],
    steps: &[(Vec<(u32, bool)>, u32, u32, u32)],
) -> Expr {
    let db0 = encode_initial_trie(clauses);
    let next0 = lit_nat(clauses.len() as u64);
    let pf = encode_refutation_lit(steps);
    Expr::apps(Expr::const_str(names::CHECK_REFUTES3), [db0, next0, pf])
}

/// `checkRefutes3 (Clean.Res.initialTrie cs) (Clean.Res.listLen cs) <steps>` — the
/// form whose type is EXACTLY [`checkRefutes3_sound`]'s hypothesis (so an
/// `Eq.refl Bool.true` cert at this term is, syntactically, the proof obligation that
/// theorem discharges).
///
/// Unlike [`check_refutes3_app`] (which pre-builds the initial trie by nested `trieIns`
/// and passes a pre-evaluated literal length), this applies the kernel `initialTrie`
/// and `listLen` DEFINITIONS to the LITERAL clause list `cs` so the kernel REDUCES them
/// itself — matching the soundness theorem's `(initialTrie cs)`/`(listLen cs)` exactly.
///
/// `cs_literal` is the SAME `List (List Nat)` term `Clean.Res.checkRefutes3_sound` is
/// instantiated at (and hence the same clause set `Unsat cs` is about); the caller
/// passes it explicitly so the cert's `cs` is bit-for-bit the bridge's clause DB. The
/// `steps` use the BigNat-id encoding ([`encode_refutation_lit`]) so the trie premise
/// lookups reduce natively (the sub-quadratic point).
///
/// The `Eq.refl` type-checks because the kernel reduces this proven form to `Bool.true`
/// on a genuine refutation (and `Bool.false` on a forged one — so it is never accepted).
pub fn check_refutes3_initialtrie_app(
    cs_literal: Expr,
    steps: &[(Vec<(u32, bool)>, u32, u32, u32)],
) -> Expr {
    let db0 = Expr::app(Expr::const_str(names::INITIAL_TRIE), cs_literal.clone());
    let next0 = Expr::app(Expr::const_str(names::LIST_LEN), cs_literal);
    let pf = encode_refutation_lit(steps);
    Expr::apps(Expr::const_str(names::CHECK_REFUTES3), [db0, next0, pf])
}

#[cfg(test)]
#[path = "resolution_check_tests.rs"]
mod tests;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Computational LRAT (RUP) trace checker — *proof by reflection*.
//!
//! # Why this exists (Program CK1, WS1-M2)
//!
//! [`crate::resolution_check`]'s `checkRefutes3` re-checks *resolution* traces.
//! The t-silicon i8 tier fits that shape, but the wide tier (i32/i64, mul/div)
//! produces LRAT traces of 10^5–10^6 steps — mechanically expanding each RUP
//! step into a resolution chain multiplies the step count by the hint count and
//! re-pays `clauseSeteq` per expanded step, so resolution-only rechecking will
//! not scale (`designs/2026-07-07-program-ck1-confluent-kernel.md`, WS1). This
//! module registers `Clean.Res.checkLrat`, a *unit-propagation* (RUP) checker
//! over the SAME clause/literal vocabulary as `checkRefutes3` (literal = `Nat`
//! `2·var+polarity`; clause = `List Nat`; clause DB = the `Clean.Res.Trie`
//! keyed by global clause id), so both checkers share one unsatisfiability
//! notion (`Clean.Res.Unsat`, [`crate::resolution_soundness`]).
//!
//! # Bool-only formulation (the trust-wp `List.Mem` escape)
//!
//! trust-wp's LRAT groundwork (`verification/clean/lrat_soundness_foundation.lean`)
//! stalled on Prop-level `List.Mem` (`∈`) resolution. Everything here is the
//! pre-scoped escape: membership / lookup / subsumption are **Bool-valued
//! recursive kernel `Definition`s** (`clauseMem`, `trieGet`, `lratReduce`) — no
//! Prop-level `List.Mem` appears in the checker or in the computational side of
//! the soundness statement ([`crate::lrat_soundness`]).
//!
//! # The checker
//!
//! ```text
//!   Clean.Res.checkLrat : Trie → Nat → List Clean.Res.LratStep → Bool
//! ```
//!
//! An LRAT step is `LratStep.mk clause hints` — the *new* clause's literals plus
//! the unit-propagation hint ids justifying it. A step is accepted iff it is
//! RUP-justified by its hints: starting from the falsified-literal set
//! `F₀ = clause` (asserting the clause's negation falsifies each of its
//! literals — stored DIRECTLY, no negation pass), the hinted clauses are
//! propagated **in order**; each hint must reduce under `F` (dropping falsified
//! literals via `lratReduce`) to either
//!
//!   * `[]`        — conflict: the step is justified (any remaining hints are
//!                   ignored; trailing unused hints are soundly irrelevant), or
//!   * `[u, u, …]` — unit (`u` plus any number of DUPLICATE copies of `u`,
//!                   checked as `listIsNil (dropLit u tail)`): `u` is forced
//!                   true, so `litNeg u` joins `F` and propagation continues
//!                   with the next hint. Duplicate-literal clauses are real —
//!                   the pinned `neg_i8` miter carries `(-1 -1 -35)` — so a
//!                   strict singleton test would refuse genuine traces,
//!
//! anything else (≥2 DISTINCT unfalsified literals, an absent/`nil` hint
//! clause, or running out of hints before conflict) refuses the step. Accepted clauses are
//! inserted into the trie at consecutive ids (`nextId`, mirroring
//! `checkRefutes3`), and the trace must terminate by deriving the EMPTY clause
//! (the last step's `clause` must be `[]`).
//!
//! Each hint is additionally guarded by `listNatIsCons (trieGet db h)`: an
//! absent id (or a genuinely-empty stored clause) fetches `nil`, which would
//! otherwise reduce to `[]` and fabricate a conflict — the guard is the
//! soundness boundary for absent hint ids (mirror of `checkRefutes3` rejecting
//! absent premises through `clauseSeteq` against `nil`).
//!
//! **Deletion steps are ignored in v1.** LRAT `d`-lines only *shrink* the
//! clause DB to speed the checker up; keeping deleted clauses live is soundly
//! conservative (a larger DB can only justify MORE steps, and every kept clause
//! is still a consequence of the original formula). The encoder simply skips
//! them.
//!
//! # Reduction-cost discipline (carrier-whnf lessons, F2/F3 context)
//!
//! Mirrors the `checkRefutes3` sub-quadratic discipline
//! (`designs/2026-06-19-checkrefutes-subquadratic.md`,
//! `designs/2026-07-06-carrier-whnf-perf.md`): all ids and literals are BigNat
//! LITERALS (`Expr::nat_lit`) so `Nat.beq`/`Nat.div`/`Nat.mod`/`Nat.ble` reduce
//! natively; clause lookups descend the `Trie` by recursing on the TRIE (never
//! `Nat.rec` on a key); the trace fold threads a literal `nextId` under native
//! `Nat.succ`; and the per-hint work is one trie descent plus
//! `O(|clause|·|F|)` native `Nat.beq`s in `lratReduce` — no `clauseSeteq`, no
//! growing-DB append, no `Or.rec` proof-tree (the certificate stays the
//! constant-size `Eq.refl`).
//!
//! # Soundness (PROVED — see [`crate::lrat_soundness`])
//!
//! `Clean.Res.checkLrat_sound : checkLrat (initialTrie cs) (listLen cs) trace =
//! true → Unsat cs` is a kernel `Theorem` with transitive axiom closure ⊆
//! FOUNDATIONAL_AXIOMS, registered by `init_lrat_soundness` (NOT auto-registered
//! here; this layer is purely computational).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::name::Name;
use crate::resolution_check::names as rnames;
use crate::{
    BinderInfo, Constructor, Declaration, EnvError, Environment, Expr, InductiveDecl,
    InductiveType, Level,
};

/// Names of the declarations the LRAT-checker layer registers.
pub mod names {
    /// `Clean.Res.LratStep` — an LRAT addition step `mk clause hints`.
    pub const LRAT_STEP: &str = "Clean.Res.LratStep";
    /// Constructor `Clean.Res.LratStep.mk (clause : List Nat) (hints : List Nat)`.
    pub const LRAT_STEP_MK: &str = "Clean.Res.LratStep.mk";
    /// `Clean.Res.lratStepClause : LratStep → List Nat` (the recorded new clause).
    pub const LRAT_STEP_CLAUSE: &str = "Clean.Res.lratStepClause";
    /// `Clean.Res.lratStepClauseEmpty : LratStep → Bool` (is the clause `[]`?).
    pub const LRAT_STEP_CLAUSE_EMPTY: &str = "Clean.Res.lratStepClauseEmpty";
    /// `Clean.Res.listLratStepIsCons : List LratStep → Bool`.
    pub const LIST_LRAT_STEP_IS_CONS: &str = "Clean.Res.listLratStepIsCons";
    /// `Clean.Res.listNatIsCons : List Nat → Bool` — the absent-hint guard
    /// (`trieGet` on an absent id returns `nil`; conflict on `nil` is refused).
    pub const LIST_NAT_IS_CONS: &str = "Clean.Res.listNatIsCons";
    /// `Clean.Res.lratReduce : List Nat → List Nat → List Nat` —
    /// `lratReduce F D` drops from `D` every literal in the falsified set `F`
    /// (Bool-valued `clauseMem` per literal; the Bool-only membership escape).
    pub const LRAT_REDUCE: &str = "Clean.Res.lratReduce";
    /// `Clean.Res.lratRup : Trie → List Nat → List Nat → Bool` —
    /// `lratRup db hints F`: propagate the hinted clauses in order from the
    /// falsified set `F`; `true` iff a hinted clause reduces to conflict.
    pub const LRAT_RUP: &str = "Clean.Res.lratRup";
    /// `Clean.Res.checkLratStep : Trie → LratStep → Bool` — one RUP step:
    /// `lratRup db hints clause` seeded with `F₀ = clause`.
    pub const CHECK_LRAT_STEP: &str = "Clean.Res.checkLratStep";
    /// `Clean.Res.checkLrat : Trie → Nat → List LratStep → Bool` — the trace
    /// fold (accepted clauses inserted at consecutive ids; last clause `[]`).
    pub const CHECK_LRAT: &str = "Clean.Res.checkLrat";
}

// ── small Expr helpers (mirrors resolution_check.rs; kept local) ───────────────

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
fn list_nat() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        nat_ty(),
    )
}
fn list_lrat_step() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        Expr::const_str(names::LRAT_STEP),
    )
}
fn list_nil(elem: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        elem,
    )
}
fn list_cons(elem: Expr, h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
        [elem, h, t],
    )
}
/// `@List.rec.{1,0} α (motive := fun _ => result_ty) nil_case cons_case major`.
fn list_rec_data(
    elem: Expr,
    result_ty: Expr,
    nil_case: Expr,
    cons_case: Expr,
    major: Expr,
) -> Expr {
    let rec = Expr::const_(
        Name::from_string("List.rec"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );
    let list_of = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        elem.clone(),
    );
    let motive = Expr::lam(BinderInfo::Default, list_of, result_ty);
    Expr::apps(rec, [elem, motive, nil_case, cons_case, major])
}
fn trie_ty() -> Expr {
    Expr::const_str(rnames::TRIE)
}
fn lit_nat(n: u64) -> Expr {
    Expr::nat_lit(n)
}
fn trie_get(db: Expr, key: Expr) -> Expr {
    Expr::apps(Expr::const_str(rnames::TRIE_GET), [db, key])
}
fn clause_mem(x: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(rnames::CLAUSE_MEM), [x, c])
}
fn lit_neg(l: Expr) -> Expr {
    Expr::app(Expr::const_str(rnames::LIT_NEG), l)
}
fn list_is_nil(c: Expr) -> Expr {
    Expr::app(Expr::const_str("Clean.Res.listIsNil"), c)
}
fn drop_lit(x: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(rnames::DROP_LIT), [x, c])
}
/// `Bool.rec (motive := fun _ => result_ty) fcase tcase scrut` (data motive).
fn bool_rec_data(result_ty: Expr, fcase: Expr, tcase: Expr, scrut: Expr) -> Expr {
    let inner_motive = Expr::lam(BinderInfo::Default, bool_ty(), result_ty);
    Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [inner_motive, fcase, tcase, scrut],
    )
}

impl Environment {
    /// Register the computational LRAT-checker layer (reflection backend).
    ///
    /// Idempotent. Requires the resolution-checker vocabulary
    /// ([`Environment::init_resolution_check`]: `clauseMem`, `litNeg`,
    /// `listIsNil`, the `Trie` with `trieGet`/`trieIns`); initializes it if
    /// absent. Every op is a reducible `Definition` with axiom closure ⊆
    /// FOUNDATIONAL_AXIOMS (none are axioms). The soundness bridge lives in
    /// [`crate::lrat_soundness`] (`init_lrat_soundness`) and is NOT
    /// auto-registered here.
    ///
    /// # Errors
    /// Propagates any [`EnvError`] from declaration insertion / kernel checking.
    pub fn init_lrat_check(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(names::CHECK_LRAT))
            .is_some()
        {
            return Ok(());
        }
        self.init_resolution_check()?;

        self.register_lrat_step_inductive()?;
        self.register_list_nat_is_cons()?;
        self.register_lrat_reduce()?;
        self.register_lrat_step_helpers()?;
        self.register_lrat_rup()?;
        self.register_check_lrat_step()?;
        self.register_check_lrat()
    }

    // ── §1 the LratStep inductive ─────────────────────────────────────────────

    fn register_lrat_step_inductive(&mut self) -> Result<(), EnvError> {
        if self
            .get_inductive(&Name::from_string(names::LRAT_STEP))
            .is_some()
        {
            return Ok(());
        }
        // inductive Clean.Res.LratStep where
        //   | mk (clause : List Nat) (hints : List Nat) : Clean.Res.LratStep
        let mk_ty = {
            let mut b = EnvDeclBuilder::new();
            let (cid, _) = b.fresh_local(list_nat());
            let (hid, _) = b.fresh_local(list_nat());
            let r = Expr::const_str(names::LRAT_STEP);
            let r = b.mk_pi(hid, BinderInfo::Default, list_nat(), r);
            let r = b.mk_pi(cid, BinderInfo::Default, list_nat(), r);
            b.finish(r)
        };
        self.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(names::LRAT_STEP),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string(names::LRAT_STEP_MK),
                    type_: mk_ty,
                }],
            }],
        })
    }

    // ── §2 listNatIsCons (the absent-hint guard) ──────────────────────────────

    fn register_list_nat_is_cons(&mut self) -> Result<(), EnvError> {
        // listNatIsCons l := List.rec false (fun _ _ _ => true) l
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (lid, l) = b.fresh_local(list_nat());
            let cons_case = Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                Expr::lam(
                    BinderInfo::Default,
                    list_nat(),
                    Expr::lam(BinderInfo::Default, bool_ty(), btrue()),
                ),
            );
            let body = list_rec_data(nat_ty(), bool_ty(), bfalse(), cons_case, l);
            b.finish(b.mk_lam(lid, BinderInfo::Default, list_nat(), body))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::LIST_NAT_IS_CONS),
            level_params: vec![],
            type_: Expr::arrow(list_nat(), bool_ty()),
            value: val,
            is_reducible: true,
        })
    }

    // ── §3 lratReduce (drop falsified literals — Bool-only membership) ────────

    fn register_lrat_reduce(&mut self) -> Result<(), EnvError> {
        // lratReduce F D := List.rec nil
        //   (fun d _t ih => Bool.rec (cons d ih) ih (clauseMem d F)) D
        // — keep d unless d ∈ F (d already falsified). Same fold shape as
        // `dropLit`, with the single-literal `litBeq` test replaced by the
        // Bool-valued set-membership `clauseMem d F`.
        let ty = Expr::arrow(list_nat(), Expr::arrow(list_nat(), list_nat()));
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (fid, f) = b.fresh_local(list_nat());
            let (did, d_c) = b.fresh_local(list_nat());
            let cons_case = {
                // bvars: ih=0, t=1, d=2 ; F is the outer fvar
                let d = Expr::bvar(2);
                let ih = Expr::bvar(0);
                let keep = list_cons(nat_ty(), d.clone(), ih.clone());
                let falsified = clause_mem(d, f.clone());
                let body = bool_rec_data(list_nat(), keep, ih, falsified);
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
            let body = list_rec_data(nat_ty(), list_nat(), list_nil(nat_ty()), cons_case, d_c);
            let e = b.mk_lam(did, BinderInfo::Default, list_nat(), body);
            b.finish(b.mk_lam(fid, BinderInfo::Default, list_nat(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::LRAT_REDUCE),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    // ── §4 step projections + list discriminator ──────────────────────────────

    fn register_lrat_step_helpers(&mut self) -> Result<(), EnvError> {
        let step_ty = Expr::const_str(names::LRAT_STEP);
        let step_rec_1 = Expr::const_(
            Name::from_string("Clean.Res.LratStep.rec"),
            vec![Level::succ(Level::zero())],
        );

        // lratStepClause s := LratStep.rec (fun clause _hints => clause) s
        let clause_val = {
            let mut b = EnvDeclBuilder::new();
            let (sid, s) = b.fresh_local(step_ty.clone());
            let motive = Expr::lam(BinderInfo::Default, step_ty.clone(), list_nat());
            // mk case: fun clause hints => clause   (bvars: hints=0, clause=1)
            let mk_case = Expr::lam(
                BinderInfo::Default,
                list_nat(),
                Expr::lam(BinderInfo::Default, list_nat(), Expr::bvar(1)),
            );
            let body = Expr::apps(step_rec_1.clone(), [motive, mk_case, s]);
            b.finish(b.mk_lam(sid, BinderInfo::Default, step_ty.clone(), body))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::LRAT_STEP_CLAUSE),
            level_params: vec![],
            type_: Expr::arrow(step_ty.clone(), list_nat()),
            value: clause_val,
            is_reducible: true,
        })?;

        // lratStepClauseEmpty s := LratStep.rec (fun clause _hints => listIsNil clause) s
        let empty_val = {
            let mut b = EnvDeclBuilder::new();
            let (sid, s) = b.fresh_local(step_ty.clone());
            let motive = Expr::lam(BinderInfo::Default, step_ty.clone(), bool_ty());
            let mk_case = Expr::lam(
                BinderInfo::Default,
                list_nat(),
                Expr::lam(BinderInfo::Default, list_nat(), list_is_nil(Expr::bvar(1))),
            );
            let body = Expr::apps(step_rec_1, [motive, mk_case, s]);
            b.finish(b.mk_lam(sid, BinderInfo::Default, step_ty.clone(), body))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::LRAT_STEP_CLAUSE_EMPTY),
            level_params: vec![],
            type_: Expr::arrow(step_ty.clone(), bool_ty()),
            value: empty_val,
            is_reducible: true,
        })?;

        // listLratStepIsCons l := List.rec false (fun _ _ _ => true) l
        let is_cons_val = {
            let mut b = EnvDeclBuilder::new();
            let (lid, l) = b.fresh_local(list_lrat_step());
            let cons_case = Expr::lam(
                BinderInfo::Default,
                step_ty.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    list_lrat_step(),
                    Expr::lam(BinderInfo::Default, bool_ty(), btrue()),
                ),
            );
            let body = list_rec_data(step_ty.clone(), bool_ty(), bfalse(), cons_case, l);
            b.finish(b.mk_lam(lid, BinderInfo::Default, list_lrat_step(), body))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::LIST_LRAT_STEP_IS_CONS),
            level_params: vec![],
            type_: Expr::arrow(list_lrat_step(), bool_ty()),
            value: is_cons_val,
            is_reducible: true,
        })
    }

    // ── §5 lratRup — the unit-propagation fold over the hint list ─────────────

    /// `lratRup db hints F`: fold the hint list, threading the falsified set
    /// `F`, and return `true` iff a hinted clause reduces to CONFLICT.
    ///
    /// ```text
    ///   lratRup db hints F₀ :=
    ///     (List.rec (motive := fun _ => List Nat → Bool)
    ///        (fun _F => false)                       -- hints exhausted: no conflict
    ///        (fun h rest ihf => fun F =>
    ///           Bool.and (listNatIsCons (trieGet db h))          -- absent-id guard
    ///             (List.rec (motive := fun _ => Bool)
    ///                true                                        -- reduce = []: CONFLICT
    ///                (fun u tail _ =>                            -- reduce = u :: tail
    ///                   Bool.rec false                           --   ≥2 distinct: refuse
    ///                            (ihf (cons (litNeg u) F))       --   unit: assert u, continue
    ///                            (listIsNil (dropLit u tail)))
    ///                (lratReduce F (trieGet db h))))
    ///        hints) F₀
    /// ```
    ///
    /// The guard `listNatIsCons (trieGet db h)` is SOUNDNESS-CRITICAL: an absent
    /// hint id fetches `nil`, whose reduction is `[]` — without the guard a
    /// forged hint would fabricate a conflict from nothing. (A genuinely-empty
    /// DB clause is also refused as a conflict hint — soundly conservative; a
    /// DB carrying `[]` is already refuted by a trace whose LAST step derives
    /// `[]` from it, which the fold's empty-clause endpoint handles.)
    ///
    /// The unit test is `listIsNil (dropLit u tail)` — the reduct is a unit iff
    /// every literal after the head is ANOTHER COPY of `u` (duplicate-literal
    /// clauses like the `neg_i8` miter's `(-1 -1 -35)` reduce to `[u, u]`,
    /// which is semantically unit). Soundness routes the duplicates through
    /// `dropFalseSat` (dropping the refuted `u` preserves satisfaction).
    fn register_lrat_rup(&mut self) -> Result<(), EnvError> {
        let acc_ty = Expr::arrow(list_nat(), bool_ty()); // F ↦ Bool
        let ty = Expr::arrow(
            trie_ty(),
            Expr::arrow(list_nat(), Expr::arrow(list_nat(), bool_ty())),
        );
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (dbid, db) = b.fresh_local(trie_ty());
            let (hintsid, hints) = b.fresh_local(list_nat());
            let (f0id, f0) = b.fresh_local(list_nat());

            // nil case : fun (_F : List Nat) => false
            let nil_case = Expr::lam(BinderInfo::Default, list_nat(), bfalse());
            // cons case : fun (h) (rest) (ihf) => fun (F) => body
            let cons_case = {
                // bvars in body: F=0, ihf=1, rest=2, h=3 ; db is the outer fvar.
                let h = Expr::bvar(3);
                let f = Expr::bvar(0);
                let d_clause = trie_get(db.clone(), h);
                let guard = Expr::app(Expr::const_str(names::LIST_NAT_IS_CONS), d_clause.clone());
                let reduced =
                    Expr::apps(Expr::const_str(names::LRAT_REDUCE), [f.clone(), d_clause]);
                // unit/conflict case split on the reduced clause:
                //   fun (u) (tail) (_ihr) =>
                //     Bool.rec false (ihf (cons (litNeg u) F))
                //              (listIsNil (dropLit u tail))
                let reduce_cons_case = {
                    // bvars: _ihr=0, tail=1, u=2 ; outer shift +3: F=3, ihf=4
                    let u = Expr::bvar(2);
                    let tail = Expr::bvar(1);
                    let ihf = Expr::bvar(4);
                    let f_in = Expr::bvar(3);
                    let new_f = list_cons(nat_ty(), lit_neg(u.clone()), f_in);
                    let go_rest = Expr::app(ihf, new_f);
                    let unit_scrut = list_is_nil(drop_lit(u, tail));
                    let body = bool_rec_data(bool_ty(), bfalse(), go_rest, unit_scrut);
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
                let step = list_rec_data(nat_ty(), bool_ty(), btrue(), reduce_cons_case, reduced);
                let body = band(guard, step);
                // fun h rest ihf F => body
                Expr::lam(
                    BinderInfo::Default,
                    nat_ty(),
                    Expr::lam(
                        BinderInfo::Default,
                        list_nat(),
                        Expr::lam(
                            BinderInfo::Default,
                            acc_ty.clone(),
                            Expr::lam(BinderInfo::Default, list_nat(), body),
                        ),
                    ),
                )
            };
            // List.rec over hints with motive (fun _ => List Nat → Bool)
            let folded = list_rec_data(nat_ty(), acc_ty.clone(), nil_case, cons_case, hints);
            let body = Expr::app(folded, f0);
            let e = b.mk_lam(f0id, BinderInfo::Default, list_nat(), body);
            let e = b.mk_lam(hintsid, BinderInfo::Default, list_nat(), e);
            b.finish(b.mk_lam(dbid, BinderInfo::Default, trie_ty(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::LRAT_RUP),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    // ── §6 checkLratStep — one RUP step, seeded with F₀ = clause ──────────────

    fn register_check_lrat_step(&mut self) -> Result<(), EnvError> {
        // checkLratStep db s := LratStep.rec
        //   (fun clause hints => lratRup db hints clause) s
        // F₀ = clause: asserting ¬clause falsifies exactly the clause's literals,
        // which are stored DIRECTLY in the falsified set (no negation pass).
        let step_ty = Expr::const_str(names::LRAT_STEP);
        let ty = Expr::arrow(trie_ty(), Expr::arrow(step_ty.clone(), bool_ty()));
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (dbid, db) = b.fresh_local(trie_ty());
            let (sid, s) = b.fresh_local(step_ty.clone());
            let step_rec = Expr::const_(
                Name::from_string("Clean.Res.LratStep.rec"),
                vec![Level::succ(Level::zero())],
            );
            let motive = Expr::lam(BinderInfo::Default, step_ty.clone(), bool_ty());
            // mk case: fun clause hints => lratRup db hints clause
            //   bvars: hints=0, clause=1 ; db is the outer fvar.
            let mk_case = {
                let clause = Expr::bvar(1);
                let hints = Expr::bvar(0);
                let body = Expr::apps(
                    Expr::const_str(names::LRAT_RUP),
                    [db.clone(), hints, clause],
                );
                Expr::lam(
                    BinderInfo::Default,
                    list_nat(),
                    Expr::lam(BinderInfo::Default, list_nat(), body),
                )
            };
            let body = Expr::apps(step_rec, [motive, mk_case, s]);
            let e = b.mk_lam(sid, BinderInfo::Default, step_ty.clone(), body);
            b.finish(b.mk_lam(dbid, BinderInfo::Default, trie_ty(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::CHECK_LRAT_STEP),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }

    // ── §7 checkLrat — the trace fold (mirror of checkRefutes3) ───────────────

    /// `checkLrat db nextId steps` — the trie-backed trace fold.
    ///
    /// ```text
    ///   checkLrat db0 nextId0 steps :=
    ///     (List.rec (motive := fun _ => Trie → Nat → Bool)
    ///        (fun _ _ => false)                       -- empty trace: no refutation
    ///        (fun s rest ih => fun db nextId =>
    ///           Bool.and (checkLratStep db s)
    ///             (Bool.rec (lratStepClauseEmpty s)   -- last step: clause must be []
    ///                       (ih (trieIns db nextId (lratStepClause s)) (Nat.succ nextId))
    ///                       (listLratStepIsCons rest)))
    ///        steps) db0 nextId0
    /// ```
    ///
    /// Identical accumulator discipline to `checkRefutes3`: the trie carries
    /// originals + accepted clauses keyed by global id, `nextId` stays a BigNat
    /// LITERAL under native `Nat.succ`.
    fn register_check_lrat(&mut self) -> Result<(), EnvError> {
        let step_ty = Expr::const_str(names::LRAT_STEP);
        let acc_ty = Expr::arrow(trie_ty(), Expr::arrow(nat_ty(), bool_ty()));
        let ty = Expr::arrow(
            trie_ty(),
            Expr::arrow(nat_ty(), Expr::arrow(list_lrat_step(), bool_ty())),
        );
        let val = {
            let mut b = EnvDeclBuilder::new();
            let (db0id, db0) = b.fresh_local(trie_ty());
            let (nid, next0) = b.fresh_local(nat_ty());
            let (stepsid, steps) = b.fresh_local(list_lrat_step());

            // nil case : fun (_db : Trie) (_nextId : Nat) => false
            let nil_case = Expr::lam(
                BinderInfo::Default,
                trie_ty(),
                Expr::lam(BinderInfo::Default, nat_ty(), bfalse()),
            );
            // cons case : fun (s) (rest) (ih) => fun (db) (nextId) => body
            let cons_case = {
                // bvars: nextId=0, db=1, ih=2, rest=3, s=4
                let s = Expr::bvar(4);
                let rest = Expr::bvar(3);
                let ih = Expr::bvar(2);
                let db = Expr::bvar(1);
                let next_id = Expr::bvar(0);
                let check_step = Expr::apps(
                    Expr::const_str(names::CHECK_LRAT_STEP),
                    [db.clone(), s.clone()],
                );
                let step_empty =
                    Expr::app(Expr::const_str(names::LRAT_STEP_CLAUSE_EMPTY), s.clone());
                let clause = Expr::app(Expr::const_str(names::LRAT_STEP_CLAUSE), s);
                let new_db = Expr::apps(
                    Expr::const_str(rnames::TRIE_INS),
                    [db, next_id.clone(), clause],
                );
                let new_next = Expr::app(Expr::const_str("Nat.succ"), next_id);
                let go_rest = Expr::apps(ih, [new_db, new_next]);
                let is_cons = Expr::app(Expr::const_str(names::LIST_LRAT_STEP_IS_CONS), rest);
                let tail = bool_rec_data(bool_ty(), step_empty, go_rest, is_cons);
                let body = band(check_step, tail);
                // fun s rest ih db nextId => body
                Expr::lam(
                    BinderInfo::Default,
                    step_ty.clone(),
                    Expr::lam(
                        BinderInfo::Default,
                        list_lrat_step(),
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
            let folded = list_rec_data(step_ty.clone(), acc_ty.clone(), nil_case, cons_case, steps);
            let body = Expr::apps(folded, [db0, next0]);
            let e = b.mk_lam(stepsid, BinderInfo::Default, list_lrat_step(), body);
            let e = b.mk_lam(nid, BinderInfo::Default, nat_ty(), e);
            b.finish(b.mk_lam(db0id, BinderInfo::Default, trie_ty(), e))
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string(names::CHECK_LRAT),
            level_params: vec![],
            type_: ty,
            value: val,
            is_reducible: true,
        })
    }
}

// ── public data-builders (tests + the t-silicon LRAT lane) ─────────────────────
//
// IDENTICAL literal/clause encoding to the `checkRefutes3` builders: a literal
// `(var, neg)` is the BigNat LITERAL `2·var + neg` (`encode_lit_lit`), a clause
// is `List Nat`, hint ids are BigNat literals. Deletion steps do not exist in
// this encoding — the LRAT `d`-lines are SKIPPED by the (untrusted) encoder
// (v1: soundly conservative, see the module docs).

use crate::resolution_check::encode_clause_lit;

/// One LRAT addition step: the new clause's literals + its RUP hint ids
/// (0-based global clause ids: originals `0..|cs|`, then one per accepted step).
pub type LratStepData = (Vec<(u32, bool)>, Vec<u64>);

/// Encode a hint-id list as a kernel `List Nat` of BigNat literals.
fn encode_hints(hints: &[u64]) -> Expr {
    let mut e = list_nil(nat_ty());
    for &h in hints.iter().rev() {
        e = list_cons(nat_ty(), lit_nat(h), e);
    }
    e
}

/// Encode one LRAT step as `Clean.Res.LratStep.mk clause hints`.
pub fn encode_lrat_step(step: &LratStepData) -> Expr {
    Expr::apps(
        Expr::const_str(names::LRAT_STEP_MK),
        [encode_clause_lit(&step.0), encode_hints(&step.1)],
    )
}

/// Encode an LRAT trace (addition steps only) as `List Clean.Res.LratStep`.
pub fn encode_lrat_trace(steps: &[LratStepData]) -> Expr {
    let mut e = list_nil(Expr::const_str(names::LRAT_STEP));
    for s in steps.iter().rev() {
        e = list_cons(Expr::const_str(names::LRAT_STEP), encode_lrat_step(s), e);
    }
    e
}

/// `checkLrat <initial-trie-of-clauses> <|clauses|> <trace>` as a kernel `Bool`
/// term, with the initial trie pre-built by nested `trieIns` (ids
/// `0..|clauses|`) — the fast-iteration twin of
/// [`check_lrat_initialtrie_app`].
pub fn check_lrat_app(clauses: &[Vec<(u32, bool)>], steps: &[LratStepData]) -> Expr {
    let db0 = crate::resolution_check::encode_initial_trie(clauses);
    let next0 = lit_nat(clauses.len() as u64);
    let pf = encode_lrat_trace(steps);
    Expr::apps(Expr::const_str(names::CHECK_LRAT), [db0, next0, pf])
}

/// `checkLrat (Clean.Res.initialTrie cs) (Clean.Res.listLen cs) <trace>` — the
/// form whose type is EXACTLY `checkLrat_sound`'s hypothesis (so an
/// `Eq.refl Bool.true` cert at this term is, syntactically, the obligation that
/// theorem discharges). `cs_literal` is the same `List (List Nat)` the bridge's
/// `Unsat cs` is about; mirror of
/// [`crate::resolution_check::check_refutes3_initialtrie_app`].
pub fn check_lrat_initialtrie_app(cs_literal: Expr, steps: &[LratStepData]) -> Expr {
    let db0 = Expr::app(Expr::const_str(rnames::INITIAL_TRIE), cs_literal.clone());
    let next0 = Expr::app(Expr::const_str(rnames::LIST_LEN), cs_literal);
    let pf = encode_lrat_trace(steps);
    Expr::apps(Expr::const_str(names::CHECK_LRAT), [db0, next0, pf])
}

#[cfg(test)]
#[path = "lrat_check_tests.rs"]
mod tests;

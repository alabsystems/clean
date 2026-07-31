// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SnSchema spec port — the SIGNATURE-SCHEMA generic recursor (task #32, the
//! 5th in-spec fragment-ladder increment after let_/Levels/Nat.rec/proj/lit).
//!
//! Generalizes the CONCRETE Nat.rec development (`natrec.rs`) to a generic
//! first-order single-sorted inductive SIGNATURE SCHEMA
//!
//!     fam : Name          -- the family name
//!     sig : ListType Nat  -- one entry per constructor: its RECURSIVE arity
//!
//! covering every first-order single-sorted inductive whose constructor
//! arguments are all of the family type itself (Nat = [0,1], Bool = [0,0],
//! binary trees = [0,2], arbitrary finite branching). Ports the guide-level,
//! census-clean development `scratch/aristotle-harvest/aristotle-sn-indexed/
//! aristotle-sn-indexed_aristotle/SnSchema.lean`
//! (FRAGMENT-SCALING INCREMENT #5, `#print axioms ⊆ [propext, Quot.sound]`).
//!
//! The generic `RecEnv`/`RecMeta`/`RecRule`/`RecRules` machinery (`rec_env.rs`)
//! and `iota_reduct`/`iota_step (env : RecEnv)` (`iota_step.rs`) are ALREADY
//! parametric — the schema INSTANTIATES them; it does not rebuild them.
//!
//! **BRICK 1 (this file, so far): the naming + const + motive + metadata LEAF
//! layer** — every construction with ZERO de Bruijn-telescope arithmetic,
//! kernel-defeq-validated against the concrete objects `natrec.rs` already
//! registers. Each `*_nat` bridge is an `Eq.refl`-bodied `def`: the embedded
//! kernel accepts it IFF the generic construction reduces to the concrete Nat
//! object, so the type-check itself IS the `rfl` validation — census-neutral
//! (Eq.refl's axiom closure is foundational-only). Any representation/index
//! mistake fails LOUDLY at its bridge, before the minorTy/genRecRhs de Bruijn
//! surgery of the later bricks.
//!
//! Registered by its own bundle stage AFTER `add_natrec_objects` (so the
//! `*_nat` bridges can reference natName/zeroName/…/natRecMeta) and, for Brick
//! 1, before `add_dependent_sn_richmodel` (no CandModel dependency yet).
//!
//! Later bricks: B2 = de Bruijn helpers (bvarSeq/piN/lamN/ihTel/mapLT) +
//! `minorTy` + minorTy_nat_{zero,succ}; B3 = genRecTy/genRecRhs/genRecRules/
//! genREnv/genRecApp + their rfls; B4 = GenRecContract/GenFresh/GenRecEnvOK +
//! the §10a' Nat→Gen bridges; B5 = the CandModel `redRecGen` field (replacing
//! `redNatRec`) + `redNatRec_gen`; B6 = the §12 SN/adequacy ladder
//! (genRecContract_steps, GenMajor, genRec_adequacy, whnf_terminates_genRec_open
//! via AccL + ZipRed) — the new CandModel-CONDITIONAL obligations (Gödel floor,
//! NOT a gap). Census stays PINNED at 11 with zero domain axioms throughout.

use crate::spec::SpecError;
use crate::spec::Specification;

impl Specification {
    /// SnSchema OBJECT prefix — Brick 1: the leaf constructions (sig
    /// representation, generic names/consts/motive/metadata) + their rfl-at-Nat
    /// validation bridges. Consumes only `add_natrec_objects` (natName/…/
    /// natRecMeta) + ListType/Name/RecMeta (early stages). Census-neutral.
    pub(super) fn add_snschema_objects(&mut self) -> Result<(), SpecError> {
        // ── Signature representation. `sig : ListType Nat`, one entry per
        // constructor = its recursive arity. sigNat = [0, 1] recovers Nat.
        self.add_recursive_def(
            "def sigNat : ListType Nat := ListType.cons Nat Nat.zero (ListType.cons Nat (Nat.succ Nat.zero) (ListType.nil Nat))",
            "The Nat signature schema [0,1] (zero: 0 recursive fields, succ: 1). SnSchema B1.",
        )?;
        // Monomorphic length over `ListType Nat` (the polymorphic `list_length`
        // in iota_step.rs is hardwired to ListType KExpr). `sigLength sigNat`
        // must reduce to 2 for genRecMeta_nat / genRecName_nat to hold by rfl.
        self.add_recursive_def(
            "def sigLength (l : ListType Nat) : Nat := ListType.rec Nat (fun (_ : ListType Nat) => Nat) Nat.zero (fun (x : Nat) (rest : ListType Nat) (ih : Nat) => Nat.succ ih) l",
            "Recursive-arity-list length (ListType Nat). Generalizes list_length. SnSchema B1.",
        )?;

        // ── Generic naming scheme: ctorName fam j = str fam j (generalizes
        // zeroName/succName); genRecName fam sig = str fam sig.length
        // (generalizes recName). Matches natrec.rs's str-tower convention.
        self.add_recursive_def(
            "def ctorName (fam : Name) (j : Nat) : Name := Name.str fam j",
            "Generic constructor-j name (str fam j). Generalizes zeroName/succName. SnSchema B1.",
        )?;
        self.add_recursive_def(
            "def genRecName (fam : Name) (sig : ListType Nat) : Name := Name.str fam (sigLength sig)",
            "Generic recursor name (str fam sig.length). Generalizes recName. SnSchema B1.",
        )?;

        // ── Generic constant heads (opaque; reduction supplied by RecEnv iota
        // rules). famTypeC/ctorC/genRecC generalize natTypeC/natZeroC.natSuccC/
        // natRecC; genMotiveTy generalizes natMotiveTy.
        self.add_recursive_def(
            "def famTypeC (fam : Name) : KExpr := KExpr.const fam (ListType.nil Level)",
            "The family type constant. Generalizes natTypeC. SnSchema B1.",
        )?;
        self.add_recursive_def(
            "def ctorC (fam : Name) (j : Nat) : KExpr := KExpr.const (ctorName fam j) (ListType.nil Level)",
            "Constructor-j constant. Generalizes natZeroC/natSuccC. SnSchema B1.",
        )?;
        self.add_recursive_def(
            "def genRecC (fam : Name) (sig : ListType Nat) (u : Level) : KExpr := KExpr.const (genRecName fam sig) (ListType.cons Level u (ListType.nil Level))",
            "The recursor constant carrying its ONE motive-universe level param. Generalizes natRecC. SnSchema B1.",
        )?;
        self.add_recursive_def(
            "def genMotiveTy (fam : Name) (u : Level) : KExpr := KExpr.pi (famTypeC fam) (KExpr.sort u)",
            "The motive type fam -> Sort u. Generalizes natMotiveTy. SnSchema B1.",
        )?;

        // ── Generic recursor metadata: RecMeta.mk num_params num_motives
        // num_minors num_indices major_after_minors, with num_minors = the
        // constructor count = sig.length. Generalizes natRecMeta.
        self.add_recursive_def(
            "def genRecMeta (sig : ListType Nat) : RecMeta := RecMeta.mk Nat.zero (Nat.succ Nat.zero) (sigLength sig) Nat.zero Bool.true",
            "Generic recursor metadata (0 params, 1 motive, sig.length minors, 0 indices, major-after-minors). Generalizes natRecMeta. SnSchema B1.",
        )?;

        // ── rfl-at-Nat validation bridges. Each is an Eq.refl-bodied def: the
        // kernel accepts it IFF the generic construction is DEFINITIONALLY EQUAL
        // to the concrete Nat object natrec.rs registered. Census-neutral.
        self.add_recursive_def(
            "def ctorName_nat_zero : Eq Name (ctorName natName Nat.zero) zeroName := Eq.refl Name zeroName",
            "rfl bridge: ctorName natName 0 = zeroName. SnSchema B1.",
        )?;
        self.add_recursive_def(
            "def ctorName_nat_succ : Eq Name (ctorName natName (Nat.succ Nat.zero)) succName := Eq.refl Name succName",
            "rfl bridge: ctorName natName 1 = succName. SnSchema B1.",
        )?;
        self.add_recursive_def(
            "def genRecName_nat : Eq Name (genRecName natName sigNat) recName := Eq.refl Name recName",
            "rfl bridge: genRecName natName sigNat = recName (validates sigLength sigNat reduces to 2). SnSchema B1.",
        )?;
        self.add_recursive_def(
            "def famTypeC_nat : Eq KExpr (famTypeC natName) natTypeC := Eq.refl KExpr natTypeC",
            "rfl bridge: famTypeC natName = natTypeC. SnSchema B1.",
        )?;
        self.add_recursive_def(
            "def ctorC_nat_zero : Eq KExpr (ctorC natName Nat.zero) natZeroC := Eq.refl KExpr natZeroC",
            "rfl bridge: ctorC natName 0 = natZeroC. SnSchema B1.",
        )?;
        self.add_recursive_def(
            "def ctorC_nat_succ : Eq KExpr (ctorC natName (Nat.succ Nat.zero)) natSuccC := Eq.refl KExpr natSuccC",
            "rfl bridge: ctorC natName 1 = natSuccC. SnSchema B1.",
        )?;
        self.add_recursive_def(
            "def genRecC_nat (u : Level) : Eq KExpr (genRecC natName sigNat u) (natRecC u) := Eq.refl KExpr (natRecC u)",
            "rfl bridge: genRecC natName sigNat u = natRecC u. SnSchema B1.",
        )?;
        self.add_recursive_def(
            "def genMotiveTy_nat (u : Level) : Eq KExpr (genMotiveTy natName u) (natMotiveTy u) := Eq.refl KExpr (natMotiveTy u)",
            "rfl bridge: genMotiveTy natName u = natMotiveTy u. SnSchema B1.",
        )?;
        self.add_recursive_def(
            "def genRecMeta_nat : Eq RecMeta (genRecMeta sigNat) natRecMeta := Eq.refl RecMeta natRecMeta",
            "rfl bridge: genRecMeta sigNat = natRecMeta (validates the 0/1/2/0/true metadata + sigLength). SnSchema B1.",
        )?;

        // ================================================================
        // BRICK 2: de Bruijn telescope helpers + the generic minor type.
        // The first GENUINE de Bruijn validation — minorTy natName 1 1 must
        // reduce to natRecSArm, and minorTy natName 0 0 to the z-arm.
        // ================================================================

        // piN dom n body: n-fold Π over a FIXED closed domain (the field-binder
        // prefix of a minor type). Structural on n; dom/body fixed.
        self.add_recursive_def(
            "def piN (dom : KExpr) (n : Nat) (body : KExpr) : KExpr := Nat.rec (fun (_ : Nat) => KExpr) body (fun (n0 : Nat) (ih : KExpr) => KExpr.pi dom ih) n",
            "n-fold Pi over a fixed closed domain. SnSchema B2.",
        )?;
        // bvarSeq top n: descending de Bruijn spine [bvar top, bvar (top-1), …]
        // of length n. Structural on n, threading `top` (decremented) via the
        // motive Nat -> ListType KExpr.
        self.add_recursive_def(
            "def bvarSeq (top : Nat) (n : Nat) : ListType KExpr := Nat.rec (fun (_ : Nat) => Nat -> ListType KExpr) (fun (t : Nat) => ListType.nil KExpr) (fun (n0 : Nat) (ih : Nat -> ListType KExpr) => fun (t : Nat) => ListType.cons KExpr (KExpr.bvar t) (ih (Nat.sub t (Nat.succ Nat.zero)))) n top",
            "Descending de Bruijn spine [bvar top, …, bvar (top-n+1)] of length n. SnSchema B2.",
        )?;
        // ihTel r c q body: the IH telescope C x_1 -> … -> C x_q, where c is the
        // CURRENT motive de Bruijn index (grows by 1 per IH binder) and the
        // targeted field sits at the CONSTANT index r-1 (the KEY invariant: each
        // IH binder pushes fields +1 while the telescope moves to the next-outer
        // field -1, cancelling). Structural on q, threading c via Nat -> KExpr.
        self.add_recursive_def(
            "def ihTel (r : Nat) (c : Nat) (q : Nat) (body : KExpr) : KExpr := Nat.rec (fun (_ : Nat) => Nat -> KExpr) (fun (c0 : Nat) => body) (fun (q0 : Nat) (ih : Nat -> KExpr) => fun (c0 : Nat) => KExpr.pi (KExpr.app (KExpr.bvar c0) (KExpr.bvar (Nat.sub r (Nat.succ Nat.zero)))) (ih (Nat.add c0 (Nat.succ Nat.zero)))) q c",
            "IH telescope C x_1 -> … -> C x_q; motive index c grows, targeted field constant at r-1. SnSchema B2.",
        )?;
        // ctorApp fam j fields: the fully-applied constructor spine c_j x_1 … x_r
        // (reuses apply_spine); the redex head of GenRecContract and the target
        // of minorTy's body.
        self.add_recursive_def(
            "def ctorApp (fam : Name) (j : Nat) (fields : ListType KExpr) : KExpr := apply_spine fields (ctorC fam j)",
            "Fully-applied constructor spine c_j x_1 … x_r. SnSchema B2.",
        )?;
        // minorTy fam j r: THE generic minor type for constructor j of recursive
        // arity r: Π(x_1..x_r : fam). C x_1 -> … -> C x_r -> C (c_j x_1..x_r),
        // authored with the motive at index j at entry. 2*r = Nat.add r r
        // (no Nat.mul primitive in the spec).
        self.add_recursive_def(
            "def minorTy (fam : Name) (j : Nat) (r : Nat) : KExpr := piN (famTypeC fam) r (ihTel r (Nat.add j r) r (KExpr.app (KExpr.bvar (Nat.add j (Nat.add r r))) (ctorApp fam j (bvarSeq (Nat.sub (Nat.add r r) (Nat.succ Nat.zero)) r))))",
            "The generic minor type for constructor j of recursive arity r. SnSchema B2.",
        )?;

        // ── rfl-at-Nat validation of the de Bruijn telescope.
        self.add_recursive_def(
            "def minorTy_nat_zero : Eq KExpr (minorTy natName Nat.zero Nat.zero) (KExpr.app (KExpr.bvar Nat.zero) natZeroC) := Eq.refl KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC)",
            "rfl bridge: minorTy natName 0 0 = the Nat zero-minor arm (C natZeroC). SnSchema B2.",
        )?;
        self.add_recursive_def(
            "def minorTy_nat_succ : Eq KExpr (minorTy natName (Nat.succ Nat.zero) (Nat.succ Nat.zero)) natRecSArm := Eq.refl KExpr natRecSArm",
            "rfl bridge: minorTy natName 1 1 = natRecSArm — the FIRST genuine de Bruijn telescope validation. SnSchema B2.",
        )?;

        // ================================================================
        // BRICK 3a: the minor Π-telescope over the signature + genRecTy.
        // Validates the ListType-Nat-threading recursion via genRecTy_nat.
        // ================================================================

        // minorsPi fam j sig body: Π-telescope over the minor types, constructor
        // index j threaded through the sig list. Recurses on sig; motive
        // Nat -> KExpr abstracts j (same accumulator idiom as apply_spine).
        self.add_recursive_def(
            "def minorsPi (fam : Name) (j : Nat) (sig : ListType Nat) (body : KExpr) : KExpr := ListType.rec Nat (fun (_ : ListType Nat) => Nat -> KExpr) (fun (j0 : Nat) => body) (fun (r : Nat) (rest : ListType Nat) (ih : Nat -> KExpr) => fun (j0 : Nat) => KExpr.pi (minorTy fam j0 r) (ih (Nat.add j0 (Nat.succ Nat.zero)))) sig j",
            "Pi-telescope over the minor types (ctor index j threaded through sig). SnSchema B3a.",
        )?;
        // genRecTy fam sig u: THE generic dependent recursor type
        // Π(C : fam -> Sort u). minor_0 -> … -> minor_(k-1) -> Π(t : fam). C t.
        self.add_recursive_def(
            "def genRecTy (fam : Name) (sig : ListType Nat) (u : Level) : KExpr := KExpr.pi (genMotiveTy fam u) (minorsPi fam Nat.zero sig (KExpr.pi (famTypeC fam) (KExpr.app (KExpr.bvar (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))))",
            "The generic dependent recursor type. Generalizes natRecTy. SnSchema B3a.",
        )?;
        self.add_recursive_def(
            "def genRecTy_nat (u : Level) : Eq KExpr (genRecTy natName sigNat u) (natRecTy u) := Eq.refl KExpr (natRecTy u)",
            "rfl bridge: genRecTy natName sigNat u = natRecTy u (validates the minor Pi-telescope + codomain). SnSchema B3a.",
        )?;
        // ════════════════════════════════════════════════════════════════════
        // B7 INDEXED-FAMILY recursor rung (fragment ladder TOP, task #33). Extends
        // the SnSchema first-order schema to INDEXED inductive families (Vec, and
        // — the prize — Nat.lt/Le/Eq, which the base Nat.rec rung provably cannot
        // reach). Same fundamental-theorem SN path: build the indexed recursor type
        // iRecTy + indexed typing env, then specialize whnf_terminates_well_typed_
        // dependent. Strategy guide: scratch/aristotle-harvest/aristotle-sn-indexed
        // (Aristotle-proven). Everything degenerates to the SnSchema rung at nIdx=0.
        // ════════════════════════════════════════════════════════════════════

        // famAppI fam iv: the family applied to an index vector, Fam i_1 … i_n.
        self.add_recursive_def(
            "def famAppI (fam : Name) (iv : ListType KExpr) : KExpr := apply_spine iv (famTypeC fam)",
            "famAppI fam iv: the family const applied to an index vector (Fam i1..in). SnSchema B7 (indexed).",
        )?;
        // motApp m ix t: the applied motive C i_1 … i_n t — the type index of the
        // logical relation for the indexed schema (the base's app m t was the
        // nIdx=0 degenerate form).
        self.add_recursive_def(
            "def motApp (m : KExpr) (ix : ListType KExpr) (t : KExpr) : KExpr := KExpr.app (apply_spine ix m) t",
            "motApp m ix t = app (apply_spine ix m) t: the motive applied to indices then major. Generalizes app m t (nIdx=0). SnSchema B7 (indexed).",
        )?;
        // iMotiveTy iFam fam nIdx u: the indexed motive type
        //   Π (i_1..i_nIdx : iFam). Fam i_1..i_nIdx → Sort u.
        // At nIdx=0 it degenerates to genMotiveTy fam u (the SnSchema motive).
        self.add_recursive_def(
            "def iMotiveTy (iFam : Name) (fam : Name) (nIdx : Nat) (u : Level) : KExpr := piN (famTypeC iFam) nIdx (KExpr.pi (famAppI fam (bvarSeq (Nat.sub nIdx (Nat.succ Nat.zero)) nIdx)) (KExpr.sort u))",
            "iMotiveTy iFam fam nIdx u: the indexed motive type (Pi over nIdx indices, then Fam idx -> Sort u). Generalizes genMotiveTy. SnSchema B7 (indexed).",
        )?;
        // iMotiveTy_deg: at nIdx=0 the indexed motive IS the SnSchema motive (piN 0
        // collapses, bvarSeq _ 0 = nil, famAppI fam nil = famTypeC fam). Validates
        // that the indexed layer degenerates exactly to the rung below it.
        self.add_recursive_def(
            "def iMotiveTy_deg (iFam : Name) (fam : Name) (u : Level) : Eq KExpr (iMotiveTy iFam fam Nat.zero u) (genMotiveTy fam u) := Eq.refl KExpr (genMotiveTy fam u)",
            "rfl bridge: iMotiveTy iFam fam 0 u = genMotiveTy fam u — the indexed motive degenerates to the SnSchema motive at nIdx=0. SnSchema B7 (indexed).",
        )?;
        // ICtor: one indexed-constructor descriptor — p index-args (a-vector), recs
        // the per-recursive-field index vectors (each a ListType KExpr), tgt the
        // constructor's TARGET index vector. The indexed signature is a ListType
        // ICtor. Generalizes the SnSchema `sig : ListType Nat` (which recorded only
        // the recursive arity r = recs.length, no index data).
        self.add_inductive(
            "inductive ICtor : Type\n| mk : forall (p : Nat) (recs : ListType (ListType KExpr)) (tgt : ListType KExpr), ICtor",
            "ICtor: an indexed-ctor descriptor (p index-args, recs recursive-field index vectors, tgt target index vector). The indexed-sig element. SnSchema B7 (indexed).",
        )?;
        self.add_recursive_def(
            "def icP (d : ICtor) : Nat := ICtor.rec (fun (_ : ICtor) => Nat) (fun (p : Nat) (recs : ListType (ListType KExpr)) (tgt : ListType KExpr) => p) d",
            "icP d: the index-arg count p of an ICtor (ICtor.rec projection). SnSchema B7 (indexed).",
        )?;
        self.add_recursive_def(
            "def icRecs (d : ICtor) : ListType (ListType KExpr) := ICtor.rec (fun (_ : ICtor) => ListType (ListType KExpr)) (fun (p : Nat) (recs : ListType (ListType KExpr)) (tgt : ListType KExpr) => recs) d",
            "icRecs d: the recursive-field index-vector list of an ICtor (ICtor.rec projection). SnSchema B7 (indexed).",
        )?;
        self.add_recursive_def(
            "def icTgt (d : ICtor) : ListType KExpr := ICtor.rec (fun (_ : ICtor) => ListType KExpr) (fun (p : Nat) (recs : ListType (ListType KExpr)) (tgt : ListType KExpr) => tgt) d",
            "icTgt d: the target index vector of an ICtor (ICtor.rec projection). SnSchema B7 (indexed).",
        )?;
        // iSigLength: number of constructors in an indexed signature (ListType.rec
        // over ListType ICtor — the ICtor analog of sigLength).
        self.add_recursive_def(
            "def iSigLength (isig : ListType ICtor) : Nat := ListType.rec ICtor (fun (_ : ListType ICtor) => Nat) Nat.zero (fun (d : ICtor) (rest : ListType ICtor) (ih : Nat) => Nat.succ ih) isig",
            "iSigLength isig: constructor count of an indexed signature. Generalizes sigLength. SnSchema B7 (indexed).",
        )?;
        // (iFieldTel / iIhTel / iMinorTy / iRecTy — the mapLT-dependent indexed
        // telescope layer — are registered LATER, after mapLT is defined below.)
        // ── B6 (corrected path): the generic CONST-TYPING env genTEnv, the analog
        // of the concrete natTEnv. clean-verify proves recursor SN via the Tait
        // fundamental theorem (whnf_terminates_well_typed_dependent) over a TypingCtx
        // whose recursor is a TYPED CONSTANT — NOT via a GenMajor accessibility
        // ladder. So generic-recursor SN = declare genRec (+ family + ctors) as typed
        // consts here, then specialize the dependent SN theorem (below).
        //
        // ctorRecTEnv: dispatches a name to its ctor type (piN famType r famType for
        // ctor j of arity r, folded over sig) or, past all ctors, the recursor type
        // genRecTy. First-order single-sorted: every ctor arg has type fam, result fam.
        self.add_recursive_def(
            "def ctorRecTEnv (fam : Name) (sig : ListType Nat) (u : Level) (j : Nat) (n : Name) : OptionType KExpr := ListType.rec Nat (fun (_ : ListType Nat) => Nat -> OptionType KExpr) (fun (j0 : Nat) => opt_pick KExpr (name_eqb n (genRecName fam sig)) (genRecTy fam sig u) (OptionType.none KExpr)) (fun (r : Nat) (rest : ListType Nat) (ih : Nat -> OptionType KExpr) => fun (j0 : Nat) => opt_pick KExpr (name_eqb n (ctorName fam j0)) (piN (famTypeC fam) r (famTypeC fam)) (ih (Nat.add j0 (Nat.succ Nat.zero)))) sig j",
            "ctorRecTEnv fam sig u j n: n's declared type if it is ctor j..k-1 (piN famType r famType) or the recursor (genRecTy), else none. The ctor+recursor half of genTEnv. SnSchema B6.",
        )?;
        // genTEnv fam sig u: the generic const-typing env — family at Sort 1 (like
        // Nat), each ctor at piN famType r famType, the recursor at genRecTy. The
        // tenv a CandModel is built over; feeds whnf_terminates_well_typed_gen.
        self.add_recursive_def(
            "def genTEnv (fam : Name) (sig : ListType Nat) (u : Level) (n : Name) : OptionType KExpr := opt_pick KExpr (name_eqb n fam) (KExpr.sort (Level.succ Level.zero)) (ctorRecTEnv fam sig u Nat.zero n)",
            "genTEnv fam sig u: the generic const-typing env (family : Sort 1, ctor j : piN famType r famType, genRec : genRecTy). Generalizes natTEnv. SnSchema B6.",
        )?;
        // (genTEnv_nat as a WHOLE-FUNCTION rfl — genTEnv natName sigNat u = natTEnv u
        // — is not rfl: under a free name the two opt_pick chains are extensionally
        // equal but the kernel won't see it without funext + per-name case analysis.
        // Deferred; not load-bearing. Instead, POINTWISE validation at each concrete
        // name confirms genTEnv assigns the intended types — these DO reduce by rfl.)
        self.add_recursive_def(
            "def genTEnv_nat_fam (u : Level) : Eq (OptionType KExpr) (genTEnv natName sigNat u natName) (OptionType.some KExpr (KExpr.sort (Level.succ Level.zero))) := Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
            "genTEnv types the family natName at Sort 1 (pointwise rfl validation). SnSchema B6.",
        )?;
        self.add_recursive_def(
            "def genTEnv_nat_rec (u : Level) : Eq (OptionType KExpr) (genTEnv natName sigNat u (genRecName natName sigNat)) (OptionType.some KExpr (genRecTy natName sigNat u)) := Eq.refl (OptionType KExpr) (OptionType.some KExpr (genRecTy natName sigNat u))",
            "genTEnv types the generic recursor at genRecTy (pointwise rfl; with genRecTy_nat this is natRecTy). Validates the recursor const-typing. SnSchema B6.",
        )?;
        self.add_recursive_def(
            "def genTEnv_nat_c0 (u : Level) : Eq (OptionType KExpr) (genTEnv natName sigNat u (ctorName natName Nat.zero)) (OptionType.some KExpr (piN (famTypeC natName) Nat.zero (famTypeC natName))) := Eq.refl (OptionType KExpr) (OptionType.some KExpr (piN (famTypeC natName) Nat.zero (famTypeC natName)))",
            "genTEnv types ctor 0 (zero) at piN famType 0 famType = famType (pointwise rfl validation). SnSchema B6.",
        )?;

        // ================================================================
        // BRICK 3b: the rule-rhs lambda + rules list + env + recursor app.
        // The hardest de Bruijn (genRecRhsBody); validated by
        // genRecRhs_nat_{zero,succ} = natRecRhs{Zero,Succ}.
        // ================================================================

        // lamN dom n body: n-fold λ over a fixed closed domain (the field-binder
        // prefix of a rule rhs).
        self.add_recursive_def(
            "def lamN (dom : KExpr) (n : Nat) (body : KExpr) : KExpr := Nat.rec (fun (_ : Nat) => KExpr) body (fun (n0 : Nat) (ih : KExpr) => KExpr.lam dom ih) n",
            "n-fold lambda over a fixed closed domain. SnSchema B3b.",
        )?;
        // mapLT f l: map over a ListType KExpr; builds the recursive-results
        // spine in genRecRhsBody.
        self.add_recursive_def(
            "def mapLT (f : KExpr -> KExpr) (l : ListType KExpr) : ListType KExpr := ListType.rec KExpr (fun (_ : ListType KExpr) => ListType KExpr) (ListType.nil KExpr) (fun (x : KExpr) (rest : ListType KExpr) (ih : ListType KExpr) => ListType.cons KExpr (f x) ih) l",
            "Map a function over a ListType KExpr. SnSchema B3b.",
        )?;
        // minorsLam fam j sig body: λ-telescope over the minor types (the rule-rhs
        // binder prefix). Same j-threaded recursion as minorsPi.
        self.add_recursive_def(
            "def minorsLam (fam : Name) (j : Nat) (sig : ListType Nat) (body : KExpr) : KExpr := ListType.rec Nat (fun (_ : ListType Nat) => Nat -> KExpr) (fun (j0 : Nat) => body) (fun (r : Nat) (rest : ListType Nat) (ih : Nat -> KExpr) => fun (j0 : Nat) => KExpr.lam (minorTy fam j0 r) (ih (Nat.add j0 (Nat.succ Nat.zero)))) sig j",
            "Lambda-telescope over the minor types (rule-rhs binder prefix). SnSchema B3b.",
        )?;
        // genRecRhsBody fam sig u j r: the reduct body of constructor j's rule —
        // m_j applied to the r fields then the r recursive-recursor-results.
        // Under [C, minors…, fields…]: m_j is bvar (r + (sig.length-1-j)); fields
        // are the descending spine bvarSeq (r-1) r; each recursive result is
        // genRec C minors… applied to that field.
        self.add_recursive_def(
            "def genRecRhsBody (fam : Name) (sig : ListType Nat) (u : Level) (j : Nat) (r : Nat) : KExpr := apply_spine (list_append (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) (KExpr.bvar (Nat.add r (Nat.sub (Nat.sub (sigLength sig) (Nat.succ Nat.zero)) j)))",
            "The rule-rhs reduct body: m_j fields (recursive results). SnSchema B3b.",
        )?;
        // ── B7 (indexed) telescope layer — placed after mapLT (used below). Feeds
        // iMinorTy → iRecTy (the indexed recursor type).
        // iFieldTel fam i recs body: the recursive-field Π-telescope of a minor type
        // — field i (i previous field binders crossed since the a⃗ params) has type
        // Fam recs_i[a⃗], its index vector lifted by i. Field counter i threaded.
        self.add_recursive_def(
            "def iFieldTel (fam : Name) (i : Nat) (recs : ListType (ListType KExpr)) (body : KExpr) : KExpr := ListType.rec (ListType KExpr) (fun (_ : ListType (ListType KExpr)) => Nat -> KExpr) (fun (i0 : Nat) => body) (fun (iv : ListType KExpr) (rest : ListType (ListType KExpr)) (ih : Nat -> KExpr) => fun (i0 : Nat) => KExpr.pi (famAppI fam (mapLT (fun (e : KExpr) => lift_at e Nat.zero i0) iv)) (ih (Nat.add i0 (Nat.succ Nat.zero)))) recs i",
            "iFieldTel fam i recs body: Pi-telescope of recursive-field domains (Fam recs_i[a], index vec lifted by field-counter i). SnSchema B7 (indexed).",
        )?;
        // iIhTel r c i recs body: the induction-hypothesis Π-telescope — the IH for
        // field i applies the motive (at de Bruijn index c, incremented under each
        // binder) to the field's index vector (lifted by r+i) and to the field
        // itself (the constant-index r-1 trick of the base's ihTel). Threads c and i.
        self.add_recursive_def(
            "def iIhTel (r : Nat) (c : Nat) (i : Nat) (recs : ListType (ListType KExpr)) (body : KExpr) : KExpr := ListType.rec (ListType KExpr) (fun (_ : ListType (ListType KExpr)) => Nat -> Nat -> KExpr) (fun (c0 : Nat) (i0 : Nat) => body) (fun (iv : ListType KExpr) (rest : ListType (ListType KExpr)) (ih : Nat -> Nat -> KExpr) => fun (c0 : Nat) (i0 : Nat) => KExpr.pi (KExpr.app (apply_spine (mapLT (fun (e : KExpr) => lift_at e Nat.zero (Nat.add r i0)) iv) (KExpr.bvar c0)) (KExpr.bvar (Nat.sub r (Nat.succ Nat.zero)))) (ih (Nat.add c0 (Nat.succ Nat.zero)) (Nat.add i0 (Nat.succ Nat.zero)))) recs c i",
            "iIhTel r c i recs body: Pi-telescope of the per-field IH domains (motive@bvar c applied to field index-vec lifted by r+i, then to field@bvar (r-1)). SnSchema B7 (indexed).",
        )?;
        // recsLen: number of recursive fields of an ICtor (length of its recs list).
        self.add_recursive_def(
            "def recsLen (recs : ListType (ListType KExpr)) : Nat := ListType.rec (ListType KExpr) (fun (_ : ListType (ListType KExpr)) => Nat) Nat.zero (fun (iv : ListType KExpr) (rest : ListType (ListType KExpr)) (ih : Nat) => Nat.succ ih) recs",
            "recsLen recs: recursive-field count of an ICtor. SnSchema B7 (indexed).",
        )?;
        // iMinorTy iFam fam j d: THE generic INDEXED minor type for ctor j —
        //   Π (a⃗ : iFam^p) (f_1 : Fam recs_1[a⃗]) … (f_r : Fam recs_r[a⃗]).
        //     C recs_1[a⃗] f_1 → … → C recs_r[a⃗] f_r → C tgt[a⃗] (c_j a⃗ f⃗).
        // Each IH sits at ITS rec-arg's index instantiation; the codomain applies the
        // motive at the ctor's TARGET index instantiation. Generalizes minorTy (which
        // had no index data). r = recsLen (icRecs d), p = icP d, 2r via r+r.
        self.add_recursive_def(
            "def iMinorTy (iFam : Name) (fam : Name) (j : Nat) (d : ICtor) : KExpr := piN (famTypeC iFam) (icP d) (iFieldTel fam Nat.zero (icRecs d) (iIhTel (recsLen (icRecs d)) (Nat.add (Nat.add j (icP d)) (recsLen (icRecs d))) Nat.zero (icRecs d) (KExpr.app (apply_spine (mapLT (fun (e : KExpr) => lift_at e Nat.zero (Nat.add (recsLen (icRecs d)) (recsLen (icRecs d)))) (icTgt d)) (KExpr.bvar (Nat.add (Nat.add j (icP d)) (Nat.add (recsLen (icRecs d)) (recsLen (icRecs d)))))) (ctorApp fam j (list_append (bvarSeq (Nat.sub (Nat.add (Nat.add (recsLen (icRecs d)) (recsLen (icRecs d))) (icP d)) (Nat.succ Nat.zero)) (icP d)) (bvarSeq (Nat.sub (Nat.add (recsLen (icRecs d)) (recsLen (icRecs d))) (Nat.succ Nat.zero)) (recsLen (icRecs d))))))))",
            "iMinorTy iFam fam j d: the indexed dependent-elimination minor type for ctor j (index-arg params, recursive-field domains iFieldTel, IH domains iIhTel, codomain = motive at the ctor target index instantiation applied to the ctor spine). Generalizes minorTy. SnSchema B7 (indexed).",
        )?;
        // iMinorTys / iMinorsPi: the indexed minor-type LIST and Π-telescope (ctor
        // index j threaded over the ISIG). Generalize minorTys / minorsPi.
        self.add_recursive_def(
            "def iMinorTys (iFam : Name) (fam : Name) (j : Nat) (isig : ListType ICtor) : ListType KExpr := ListType.rec ICtor (fun (_ : ListType ICtor) => Nat -> ListType KExpr) (fun (j0 : Nat) => ListType.nil KExpr) (fun (d : ICtor) (rest : ListType ICtor) (ih : Nat -> ListType KExpr) => fun (j0 : Nat) => ListType.cons KExpr (iMinorTy iFam fam j0 d) (ih (Nat.add j0 (Nat.succ Nat.zero)))) isig j",
            "iMinorTys iFam fam j isig: the indexed minor-type list (ctor index j threaded over isig). Generalizes minorTys. SnSchema B7 (indexed).",
        )?;
        self.add_recursive_def(
            "def iMinorsPi (iFam : Name) (fam : Name) (j : Nat) (isig : ListType ICtor) (body : KExpr) : KExpr := ListType.rec ICtor (fun (_ : ListType ICtor) => Nat -> KExpr) (fun (j0 : Nat) => body) (fun (d : ICtor) (rest : ListType ICtor) (ih : Nat -> KExpr) => fun (j0 : Nat) => KExpr.pi (iMinorTy iFam fam j0 d) (ih (Nat.add j0 (Nat.succ Nat.zero)))) isig j",
            "iMinorsPi iFam fam j isig body: Pi-telescope over the indexed minor types. Generalizes minorsPi. SnSchema B7 (indexed).",
        )?;
        // iRecTy iFam fam nIdx isig u: THE INDEXED DEPENDENT RECURSOR TYPE —
        //   Π (C : Π i⃗. Fam i⃗ → Sort u). minors → Π (i⃗ : iFam^nIdx) (t : Fam i⃗). C i⃗ t.
        // The B7 analog of genRecTy (the codomain now applies the motive to the
        // major's index vector bvarSeq nIdx nIdx, then the major bvar 0).
        self.add_recursive_def(
            "def iRecTy (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) : KExpr := KExpr.pi (iMotiveTy iFam fam nIdx u) (iMinorsPi iFam fam Nat.zero isig (piN (famTypeC iFam) nIdx (KExpr.pi (famAppI fam (bvarSeq (Nat.sub nIdx (Nat.succ Nat.zero)) nIdx)) (motApp (KExpr.bvar (Nat.add (Nat.add (iSigLength isig) nIdx) (Nat.succ Nat.zero))) (bvarSeq nIdx nIdx) (KExpr.bvar Nat.zero)))))",
            "iRecTy iFam fam nIdx isig u: THE indexed dependent recursor type (motive over indices, indexed minors, then Pi indices + major -> motive at those indices applied to the major). Generalizes genRecTy. SnSchema B7 (indexed).",
        )?;
        // iRecName: the indexed recursor's name (Name.str fam #ctors). Generalizes
        // genRecName. iCtorTy: the DECLARED type of indexed ctor j —
        //   Π (a⃗ : iFam^p) (f_1 : Fam recs_1[a⃗]) … (f_r : Fam recs_r[a⃗]). Fam tgt[a⃗]
        // (index-params, the recursive-field telescope iFieldTel, codomain the family
        // at the ctor's TARGET index vector, lifted by r past the field binders).
        // These + iRecTy are what the indexed const-typing env declares.
        self.add_recursive_def(
            "def iRecName (fam : Name) (isig : ListType ICtor) : Name := Name.str fam (iSigLength isig)",
            "iRecName fam isig: the indexed recursor's name. Generalizes genRecName. SnSchema B7 (indexed).",
        )?;
        self.add_recursive_def(
            "def iCtorTy (iFam : Name) (fam : Name) (d : ICtor) : KExpr := piN (famTypeC iFam) (icP d) (iFieldTel fam Nat.zero (icRecs d) (famAppI fam (mapLT (fun (e : KExpr) => lift_at e Nat.zero (recsLen (icRecs d))) (icTgt d))))",
            "iCtorTy iFam fam d: the declared type of an indexed ctor (index-params + recursive-field telescope + codomain Fam tgt, tgt lifted past the field binders). The indexed analog of piN famType r famType. SnSchema B7 (indexed).",
        )?;
        // iCtorRecTEnv / iTEnv: the indexed const-typing env, the analog of
        // ctorRecTEnv / genTEnv. iCtorRecTEnv dispatches a name to its ctor type
        // (iCtorTy, folded over isig) or, past all ctors, the indexed recursor type
        // (iRecTy). iTEnv puts the family at Π(indices).Sort 1 (like Nat.lt : Nat ->
        // Nat -> Type), each ctor at iCtorTy, the recursor at iRecTy.
        self.add_recursive_def(
            "def iCtorRecTEnv (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) (j : Nat) (n : Name) : OptionType KExpr := ListType.rec ICtor (fun (_ : ListType ICtor) => Nat -> OptionType KExpr) (fun (j0 : Nat) => opt_pick KExpr (name_eqb n (iRecName fam isig)) (iRecTy iFam fam nIdx isig u) (OptionType.none KExpr)) (fun (d : ICtor) (rest : ListType ICtor) (ih : Nat -> OptionType KExpr) => fun (j0 : Nat) => opt_pick KExpr (name_eqb n (ctorName fam j0)) (iCtorTy iFam fam d) (ih (Nat.add j0 (Nat.succ Nat.zero)))) isig j",
            "iCtorRecTEnv iFam fam nIdx isig u j n: n's declared type if it is an indexed ctor (iCtorTy) or the indexed recursor (iRecTy), else none. The ctor+recursor half of iTEnv. SnSchema B7 (indexed).",
        )?;
        self.add_recursive_def(
            "def iTEnv (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) (n : Name) : OptionType KExpr := opt_pick KExpr (name_eqb n fam) (piN (famTypeC iFam) nIdx (KExpr.sort (Level.succ Level.zero))) (iCtorRecTEnv iFam fam nIdx isig u Nat.zero n)",
            "iTEnv iFam fam nIdx isig u: the indexed const-typing env (family : Pi(indices) Sort 1, indexed ctor : iCtorTy, indexed recursor : iRecTy). Generalizes genTEnv/natTEnv to indexed families. SnSchema B7 (indexed).",
        )?;
        // ── B7 CONCRETE: Nat.lt as an indexed family (the fragment ladder's
        // motivating example — Nat.lt : Nat -> Nat -> Type IS an indexed family the
        // base Nat.rec rung cannot reach). ltName + sigLt (2 ICtors: zero_lt_succ
        // ⟨1,[],[0, succ n]⟩ and succ_lt_succ ⟨2,[[n,m]],[succ n, succ m]⟩).
        self.add_recursive_def(
            "def ltName : Name := Name.str Name.anonymous (Nat.succ (Nat.succ Nat.zero))",
            "ltName: the Nat.lt family name (Name.str anonymous 2). SnSchema B7 (indexed, Lt instance).",
        )?;
        self.add_recursive_def(
            "def dZeroLtSucc : ICtor := ICtor.mk (Nat.succ Nat.zero) (ListType.nil (ListType KExpr)) (ListType.cons KExpr natZeroC (ListType.cons KExpr (KExpr.app natSuccC (KExpr.bvar Nat.zero)) (ListType.nil KExpr)))",
            "dZeroLtSucc: the zero_lt_succ ICtor (p=1, no rec fields, target [0, succ n]). SnSchema B7 (Lt).",
        )?;
        self.add_recursive_def(
            "def dSuccLtSucc : ICtor := ICtor.mk (Nat.succ (Nat.succ Nat.zero)) (ListType.cons (ListType KExpr) (ListType.cons KExpr (KExpr.bvar (Nat.succ Nat.zero)) (ListType.cons KExpr (KExpr.bvar Nat.zero) (ListType.nil KExpr))) (ListType.nil (ListType KExpr))) (ListType.cons KExpr (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))) (ListType.cons KExpr (KExpr.app natSuccC (KExpr.bvar Nat.zero)) (ListType.nil KExpr)))",
            "dSuccLtSucc: the succ_lt_succ ICtor (p=2, one rec field at [n,m], target [succ n, succ m]). SnSchema B7 (Lt).",
        )?;
        self.add_recursive_def(
            "def sigLt : ListType ICtor := ListType.cons ICtor dZeroLtSucc (ListType.cons ICtor dSuccLtSucc (ListType.nil ICtor))",
            "sigLt: Nat.lt's indexed signature [dZeroLtSucc, dSuccLtSucc]. SnSchema B7 (Lt).",
        )?;
        // Pointwise validation: iTEnv types Lt's ctor 0 at iCtorTy and the recursor
        // at iRecTy (concrete-name dispatch reduces by rfl) — confirms the indexed
        // typing env is MEANINGFUL for the flagship indexed family.
        self.add_recursive_def(
            "def iTEnv_lt_c0 (u : Level) : Eq (OptionType KExpr) (iTEnv natName ltName (Nat.succ (Nat.succ Nat.zero)) sigLt u (ctorName ltName Nat.zero)) (OptionType.some KExpr (iCtorTy natName ltName dZeroLtSucc)) := Eq.refl (OptionType KExpr) (OptionType.some KExpr (iCtorTy natName ltName dZeroLtSucc))",
            "iTEnv types Lt ctor 0 (zero_lt_succ) at iCtorTy dZeroLtSucc (pointwise rfl). SnSchema B7 (Lt validation).",
        )?;
        self.add_recursive_def(
            "def iTEnv_lt_rec (u : Level) : Eq (OptionType KExpr) (iTEnv natName ltName (Nat.succ (Nat.succ Nat.zero)) sigLt u (iRecName ltName sigLt)) (OptionType.some KExpr (iRecTy natName ltName (Nat.succ (Nat.succ Nat.zero)) sigLt u)) := Eq.refl (OptionType KExpr) (OptionType.some KExpr (iRecTy natName ltName (Nat.succ (Nat.succ Nat.zero)) sigLt u))",
            "iTEnv types the Lt recursor at iRecTy (pointwise rfl) — validates the indexed recursor typing dispatch. SnSchema B7 (Lt validation).",
        )?;
        // genRecRhs fam sig u j r: the full rule rhs — λC. λminors. λfields. body.
        self.add_recursive_def(
            "def genRecRhs (fam : Name) (sig : ListType Nat) (u : Level) (j : Nat) (r : Nat) : KExpr := KExpr.lam (genMotiveTy fam u) (minorsLam fam Nat.zero sig (lamN (famTypeC fam) r (genRecRhsBody fam sig u j r)))",
            "The full recursor-rule rhs lambda. Generalizes natRecRhsZero/Succ. SnSchema B3b.",
        )?;
        // genRecRulesFrom fam sig u j rest: RecRules over the sig suffix `rest`,
        // ctor index j threaded; each rule uses the FULL sig for its rhs.
        self.add_recursive_def(
            "def genRecRulesFrom (fam : Name) (sig : ListType Nat) (u : Level) (j : Nat) (rest : ListType Nat) : RecRules := ListType.rec Nat (fun (_ : ListType Nat) => Nat -> RecRules) (fun (j0 : Nat) => RecRules.nil) (fun (r : Nat) (rest0 : ListType Nat) (ih : Nat -> RecRules) => fun (j0 : Nat) => RecRules.cons (RecRule.mk (ctorName fam j0) r (genRecRhs fam sig u j0 r)) (ih (Nat.add j0 (Nat.succ Nat.zero)))) rest j",
            "RecRules over the sig suffix (ctor index threaded). SnSchema B3b.",
        )?;
        self.add_recursive_def(
            "def genRecRules (fam : Name) (sig : ListType Nat) (u : Level) : RecRules := genRecRulesFrom fam sig u Nat.zero sig",
            "The generic recursor rules list. Generalizes natRecRules. SnSchema B3b.",
        )?;
        // genREnv fam sig u: the single-recursor RecEnv. Generalizes natREnv.
        self.add_recursive_def(
            "def genREnv (fam : Name) (sig : ListType Nat) (u : Level) : RecEnv := RecEnv.addRec RecEnv.empty (genRecName fam sig) (genRecMeta sig) (genRecRules fam sig u)",
            "The generic single-recursor RecEnv. Generalizes natREnv. SnSchema B3b.",
        )?;
        // genRecApp fam sig u m ms t: the fully-applied recursor spine
        // genRec.{u} m minors… t. Generalizes natRecApp.
        self.add_recursive_def(
            "def genRecApp (fam : Name) (sig : ListType Nat) (u : Level) (m : KExpr) (ms : ListType KExpr) (t : KExpr) : KExpr := apply_spine (ListType.cons KExpr m (list_append ms (ListType.cons KExpr t (ListType.nil KExpr)))) (genRecC fam sig u)",
            "The fully-applied recursor spine. Generalizes natRecApp. SnSchema B3b.",
        )?;

        // ── rfl-at-Nat validation of the rhs/rules/env/app assembly.
        self.add_recursive_def(
            "def genRecRhs_nat_zero (u : Level) : Eq KExpr (genRecRhs natName sigNat u Nat.zero Nat.zero) (natRecRhsZero u) := Eq.refl KExpr (natRecRhsZero u)",
            "rfl bridge: genRecRhs natName sigNat u 0 0 = natRecRhsZero u. SnSchema B3b.",
        )?;
        self.add_recursive_def(
            "def genRecRhs_nat_succ (u : Level) : Eq KExpr (genRecRhs natName sigNat u (Nat.succ Nat.zero) (Nat.succ Nat.zero)) (natRecRhsSucc u) := Eq.refl KExpr (natRecRhsSucc u)",
            "rfl bridge: genRecRhs natName sigNat u 1 1 = natRecRhsSucc u — the HARDEST de Bruijn validation (genRecRhsBody). SnSchema B3b.",
        )?;
        self.add_recursive_def(
            "def genRecRules_nat (u : Level) : Eq RecRules (genRecRules natName sigNat u) (natRecRules u) := Eq.refl RecRules (natRecRules u)",
            "rfl bridge: genRecRules natName sigNat u = natRecRules u. SnSchema B3b.",
        )?;
        self.add_recursive_def(
            "def genREnv_nat (u : Level) : Eq RecEnv (genREnv natName sigNat u) (natREnv u) := Eq.refl RecEnv (natREnv u)",
            "rfl bridge: genREnv natName sigNat u = natREnv u. SnSchema B3b.",
        )?;
        self.add_recursive_def(
            "def genRecApp_nat (u : Level) (m : KExpr) (z : KExpr) (s : KExpr) (t : KExpr) : Eq KExpr (genRecApp natName sigNat u m (ListType.cons KExpr z (ListType.cons KExpr s (ListType.nil KExpr))) t) (natRecApp u m z s t) := Eq.refl KExpr (natRecApp u m z s t)",
            "rfl bridge: genRecApp natName sigNat u m [z,s] t = natRecApp u m z s t. SnSchema B3b.",
        )?;

        // ================================================================
        // BRICK 4a: signature/minor lookups + the object-level computation
        // rule (GenRecContract) + the δ-freshness / env-correctness gates,
        // generalizing NatRecContract / NatFresh / NatRecEnvOK.
        // ================================================================

        // sigGet sig j: the recursive arity of constructor j (list index).
        self.add_recursive_def(
            "def sigGet (sig : ListType Nat) (j : Nat) : OptionType Nat := ListType.rec Nat (fun (_ : ListType Nat) => Nat -> OptionType Nat) (fun (j0 : Nat) => OptionType.none Nat) (fun (r : Nat) (rest : ListType Nat) (ih : Nat -> OptionType Nat) => fun (j0 : Nat) => Nat.rec (fun (_ : Nat) => OptionType Nat) (OptionType.some Nat r) (fun (j1 : Nat) (_ : OptionType Nat) => ih j1) j0) sig j",
            "Recursive-arity lookup of constructor j in the signature. SnSchema B4a.",
        )?;
        // listGet ms j: positional lookup into the minor list (selects minor m_j).
        self.add_recursive_def(
            "def listGet (l : ListType KExpr) (j : Nat) : OptionType KExpr := ListType.rec KExpr (fun (_ : ListType KExpr) => Nat -> OptionType KExpr) (fun (j0 : Nat) => OptionType.none KExpr) (fun (x : KExpr) (rest : ListType KExpr) (ih : Nat -> OptionType KExpr) => fun (j0 : Nat) => Nat.rec (fun (_ : Nat) => OptionType KExpr) (OptionType.some KExpr x) (fun (j1 : Nat) (_ : OptionType KExpr) => ih j1) j0) l j",
            "Positional lookup into the minor list (selects m_j). SnSchema B4a.",
        )?;
        // genContractum fam sig u m ms mj fields: the reduct of constructor j's
        // iota rule — m_j applied to the r fields then the r recursive results
        // rec m ms f_i. (This is genRecRhsBody realized on ACTUAL field terms.)
        self.add_recursive_def(
            "def genContractum (fam : Name) (sig : ListType Nat) (u : Level) (m : KExpr) (ms : ListType KExpr) (mj : KExpr) (fields : ListType KExpr) : KExpr := apply_spine (list_append fields (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields)) mj",
            "The iota-rule reduct: m_j fields (rec m ms f_1) … (rec m ms f_r). SnSchema B4a.",
        )?;

        // GenRecContract: the object-level computation rule schema
        //   rec m ms (c_j f_1 … f_r) ~> m_j f_1 … f_r (rec m ms f_1) … (rec m ms f_r)
        // ONE rule replaces NatRecContract's per-ctor zero/succ (Type-valued so
        // it large-eliminates in the SN ladder).
        self.add_inductive(
            "inductive GenRecContract (fam : Name) (sig : ListType Nat) (u : Level) : KExpr -> KExpr -> Type\n| rule : forall (j : Nat) (r : Nat) (m : KExpr) (mj : KExpr) (ms : ListType KExpr) (fields : ListType KExpr), Eq (OptionType Nat) (sigGet sig j) (OptionType.some Nat r) -> Eq Nat (list_length ms) (sigLength sig) -> Eq (OptionType KExpr) (listGet ms j) (OptionType.some KExpr mj) -> Eq Nat (list_length fields) r -> GenRecContract fam sig u (genRecApp fam sig u m ms (ctorApp fam j fields)) (genContractum fam sig u m ms mj fields)",
            "GenRecContract fam sig u lhs rhs: the generic object-level iota rule schema. Generalizes NatRecContract. SnSchema B4a.",
        )?;
        // GenFresh: denv δ-defines none of fam / any ctorName (bounded by
        // sig.length) / genRecName. Generalizes NatFresh.
        self.add_inductive(
            "inductive GenFresh (fam : Name) (sig : ListType Nat) : DefEnv -> Type\n| mk : forall (denv : DefEnv), Eq (OptionType KExpr) (defval_for denv fam) (OptionType.none KExpr) -> (forall (j : Nat), Lt j (sigLength sig) -> Eq (OptionType KExpr) (defval_for denv (ctorName fam j)) (OptionType.none KExpr)) -> Eq (OptionType KExpr) (defval_for denv (genRecName fam sig)) (OptionType.none KExpr) -> GenFresh fam sig denv",
            "GenFresh fam sig denv: denv δ-defines none of the family's names. Generalizes NatFresh. SnSchema B4a.",
        )?;
        // GenRecEnvOK: renv carries the recursor metadata + every rule (one rule
        // conjunct per constructor, quantified over sig). Generalizes NatRecEnvOK.
        self.add_inductive(
            "inductive GenRecEnvOK (fam : Name) (sig : ListType Nat) (u : Level) : RecEnv -> Type\n| mk : forall (renv : RecEnv), Eq (OptionType RecMeta) (recmeta_for renv (genRecName fam sig)) (OptionType.some RecMeta (genRecMeta sig)) -> (forall (j : Nat) (r : Nat), Eq (OptionType Nat) (sigGet sig j) (OptionType.some Nat r) -> Eq (OptionType RecRule) (recrule_for renv (genRecName fam sig) (ctorName fam j)) (OptionType.some RecRule (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)))) -> GenRecEnvOK fam sig u renv",
            "GenRecEnvOK fam sig u renv: renv carries the recursor metadata + every rule. Generalizes NatRecEnvOK. SnSchema B4a.",
        )?;
        // WhnfAccAll xs: every element of xs is whnf_acc. The generic recursor's
        // minors list ms carries one whnf_acc per minor (the guide phrases this as
        // `forall x, MemL x ms -> whnf_acc x`; WhnfAccAll is the equivalent
        // clean-verify idiom, term-mode-trivial to BUILD and PROJECT). This is the
        // "all minors are whnf_acc" clause of the B5 redRecGen CandModel field.
        self.add_inductive(
            "inductive WhnfAccAll : ListType KExpr -> Type\n| nil : WhnfAccAll (ListType.nil KExpr)\n| cons : forall (x : KExpr) (rest : ListType KExpr), whnf_acc x -> WhnfAccAll rest -> WhnfAccAll (ListType.cons KExpr x rest)",
            "WhnfAccAll xs: every element of xs is whnf_acc (nil + cons carrying whnf_acc head). The minors-list clause of the generic redRecGen field. Generalizes the per-minor whnf_acc premises. SnSchema B5.",
        )?;
        // whnfAccAll_cons2: the Nat instance builder — WhnfAccAll [z,s] from
        // whnf_acc z + whnf_acc s. Feeds redNatRec_holds's Nat specialization of
        // the generic redRecGen field (ms = [z, s] for Nat's [zero-minor, succ-minor]).
        self.add_recursive_def(
            "def whnfAccAll_cons2 (z : KExpr) (s : KExpr) (hz : whnf_acc z) (hs : whnf_acc s) : WhnfAccAll (ListType.cons KExpr z (ListType.cons KExpr s (ListType.nil KExpr))) := WhnfAccAll.cons z (ListType.cons KExpr s (ListType.nil KExpr)) hz (WhnfAccAll.cons s (ListType.nil KExpr) hs (WhnfAccAll.nil))",
            "WhnfAccAll [z,s] from whnf_acc z + whnf_acc s (two WhnfAccAll.cons + nil). The Nat minors-list witness for redNatRec_holds's specialization of redRecGen. SnSchema B5.",
        )?;
        // lt_zero_empty: Lt n 0 is uninhabited (both Lt ctors — zero_lt_succ /
        // succ_lt_succ — target a succ index). An EARLY clone of the PROVEN
        // not_lt_zero (impl-soundness, which registers at a LATER bundle stage than
        // add_snschema_objects) via the ltzero_goal motive alias, so the relocated
        // natFresh_ctor_field's j>=2 vacuous case (Empty.rec into its Prop goal)
        // resolves here in step B. Empty : Type, so the motive stays Type-uniform.
        self.add_recursive_def(
            "def ltzero_goal (a : Nat) (b : Nat) (h : Lt a b) : Type := Nat.rec (fun (_ : Nat) => Type) Empty (fun (_ : Nat) (_ : Type) => Nat) b",
            "Semireducible Lt-to-Empty motive alias: Empty at b=0, Nat at b=succ. Early not_lt_zero_goal clone for step B. SnSchema B5.",
        )?;
        self.add_recursive_def(
            "def lt_zero_empty (n : Nat) (h : Lt n Nat.zero) : Empty := Lt.rec ltzero_goal (fun (k : Nat) => Nat.zero) (fun (k : Nat) (m : Nat) (hltkm : Lt k m) (_ih : ltzero_goal k m hltkm) => Nat.zero) n Nat.zero h",
            "Lt n 0 -> Empty (Lt.rec with the ltzero_goal large-elim motive; both ctors hit a succ index so minors return Nat.zero, target index 0 gives Empty). Early not_lt_zero clone for step B. SnSchema B5.",
        )?;

        // ── B4b §10a: the Nat→Gen bridges (RELOCATED here from add_snschema so the
        // B5 redNatRec_holds re-body — deriving the Nat redNatRec adequacy from the
        // generic redRecGen CandModel field — can consume them before step C's
        // CandModel/redNatRec_holds). Each maps a CONCRETE Nat gate/relation to its
        // generic instance at (natName, sigNat): the concrete Nat.rec development IS
        // the schema at sig=[0,1], the generic objects reducing to concrete by rfl.
        self.add_recursive_def(
            "def natContract_to_gen (u : Level) (lhs : KExpr) (rhs : KExpr) (h : NatRecContract u lhs rhs) : GenRecContract natName sigNat u lhs rhs := NatRecContract.rec u (fun (e0 : KExpr) (e0b : KExpr) (_ : NatRecContract u e0 e0b) => GenRecContract natName sigNat u e0 e0b) (fun (m : KExpr) (z : KExpr) (s : KExpr) => GenRecContract.rule natName sigNat u Nat.zero Nat.zero m z (ListType.cons KExpr z (ListType.cons KExpr s (ListType.nil KExpr))) (ListType.nil KExpr) (Eq.refl (OptionType Nat) (OptionType.some Nat Nat.zero)) (Eq.refl Nat (Nat.succ (Nat.succ Nat.zero))) (Eq.refl (OptionType KExpr) (OptionType.some KExpr z)) (Eq.refl Nat Nat.zero)) (fun (m : KExpr) (z : KExpr) (s : KExpr) (n : KExpr) => GenRecContract.rule natName sigNat u (Nat.succ Nat.zero) (Nat.succ Nat.zero) m s (ListType.cons KExpr z (ListType.cons KExpr s (ListType.nil KExpr))) (ListType.cons KExpr n (ListType.nil KExpr)) (Eq.refl (OptionType Nat) (OptionType.some Nat (Nat.succ Nat.zero))) (Eq.refl Nat (Nat.succ (Nat.succ Nat.zero))) (Eq.refl (OptionType KExpr) (OptionType.some KExpr s)) (Eq.refl Nat (Nat.succ Nat.zero))) lhs rhs h",
            "NatRecContract u lhs rhs -> GenRecContract natName sigNat u lhs rhs: the concrete Nat.rec iota relation is the schema instance at sig=[0,1]. SnSchema B4b §10a.",
        )?;
        self.add_recursive_def(
            "def natFresh_ctor_field (d : DefEnv) (h1 : Eq (OptionType KExpr) (defval_for d zeroName) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (defval_for d succName) (OptionType.none KExpr)) (j : Nat) (hlt : Lt j (sigLength sigNat)) : Eq (OptionType KExpr) (defval_for d (ctorName natName j)) (OptionType.none KExpr) := Nat.rec (fun (j0 : Nat) => Lt j0 (sigLength sigNat) -> Eq (OptionType KExpr) (defval_for d (ctorName natName j0)) (OptionType.none KExpr)) (fun (hz0 : Lt Nat.zero (sigLength sigNat)) => h1) (fun (j' : Nat) (ih1 : Lt j' (sigLength sigNat) -> Eq (OptionType KExpr) (defval_for d (ctorName natName j')) (OptionType.none KExpr)) => Nat.rec (fun (j1 : Nat) => Lt (Nat.succ j1) (sigLength sigNat) -> Eq (OptionType KExpr) (defval_for d (ctorName natName (Nat.succ j1))) (OptionType.none KExpr)) (fun (hz1 : Lt (Nat.succ Nat.zero) (sigLength sigNat)) => h2) (fun (j'' : Nat) (ih2 : Lt (Nat.succ j'') (sigLength sigNat) -> Eq (OptionType KExpr) (defval_for d (ctorName natName (Nat.succ j''))) (OptionType.none KExpr)) => fun (hj2 : Lt (Nat.succ (Nat.succ j'')) (sigLength sigNat)) => Empty.rec (fun (he : Empty) => Eq (OptionType KExpr) (defval_for d (ctorName natName (Nat.succ (Nat.succ j'')))) (OptionType.none KExpr)) (lt_zero_empty j'' (lt_succ_succ_to_lt j'' Nat.zero (lt_succ_succ_to_lt (Nat.succ j'') (Nat.succ Nat.zero) hj2)))) j') j hlt",
            "The forall-j ctor-freshness field of GenFresh at (natName, sigNat): j=0/1 -> zero/succ freshness, j>=2 vacuous (via lt_zero_elim on the peeled Lt j'' 0). SnSchema B4b §10a helper.",
        )?;
        self.add_recursive_def(
            "def natGenFresh_witness (d : DefEnv) (h0 : Eq (OptionType KExpr) (defval_for d natName) (OptionType.none KExpr)) (h1 : Eq (OptionType KExpr) (defval_for d zeroName) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (defval_for d succName) (OptionType.none KExpr)) (h3 : Eq (OptionType KExpr) (defval_for d recName) (OptionType.none KExpr)) : GenFresh natName sigNat d := GenFresh.mk natName sigNat d h0 (natFresh_ctor_field d h1 h2) h3",
            "GenFresh.mk assembly at (natName, sigNat) from the four NatFresh freshness fields. SnSchema B4b §10a helper.",
        )?;
        self.add_recursive_def(
            "def natFresh_to_genFresh (denv : DefEnv) (hf : NatFresh denv) : GenFresh natName sigNat denv := NatFresh.rec (fun (_ : NatFresh denv) => GenFresh natName sigNat denv) (fun (h0 : Eq (OptionType KExpr) (defval_for denv natName) (OptionType.none KExpr)) (h1 : Eq (OptionType KExpr) (defval_for denv zeroName) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (defval_for denv succName) (OptionType.none KExpr)) (h3 : Eq (OptionType KExpr) (defval_for denv recName) (OptionType.none KExpr)) => natGenFresh_witness denv h0 h1 h2 h3) hf",
            "NatFresh denv -> GenFresh natName sigNat denv: Nat δ-freshness is generic δ-freshness at sig=[0,1] (1-arg motive; denv param-promoted). SnSchema B4b §10a.",
        )?;
        self.add_recursive_def(
            "def natRecEnvOK_to_gen (u : Level) (renv : RecEnv) (hok : NatRecEnvOK u renv) : GenRecEnvOK natName sigNat u renv := NatRecEnvOK.rec (fun (_ : NatRecEnvOK u renv) => GenRecEnvOK natName sigNat u renv) (fun (hmeta : Eq (OptionType RecMeta) (recmeta_for renv recName) (OptionType.some RecMeta natRecMeta)) (hzero : Eq (OptionType RecRule) (recrule_for renv recName zeroName) (OptionType.some RecRule (RecRule.mk zeroName Nat.zero (natRecRhsZero u)))) (hsucc : Eq (OptionType RecRule) (recrule_for renv recName succName) (OptionType.some RecRule (RecRule.mk succName (Nat.succ Nat.zero) (natRecRhsSucc u)))) => GenRecEnvOK.mk natName sigNat u renv hmeta (fun (j : Nat) => Nat.rec (fun (j0 : Nat) => forall (r : Nat), Eq (OptionType Nat) (sigGet sigNat j0) (OptionType.some Nat r) -> Eq (OptionType RecRule) (recrule_for renv (genRecName natName sigNat) (ctorName natName j0)) (OptionType.some RecRule (RecRule.mk (ctorName natName j0) r (genRecRhs natName sigNat u j0 r)))) (fun (r : Nat) (hjr : Eq (OptionType Nat) (sigGet sigNat Nat.zero) (OptionType.some Nat r)) => Eq.substType Nat (fun (rr : Nat) => Eq (OptionType RecRule) (recrule_for renv (genRecName natName sigNat) (ctorName natName Nat.zero)) (OptionType.some RecRule (RecRule.mk (ctorName natName Nat.zero) rr (genRecRhs natName sigNat u Nat.zero rr)))) Nat.zero r (option_some_inj Nat Nat.zero r hjr) hzero) (fun (j' : Nat) (ih1r : forall (r : Nat), Eq (OptionType Nat) (sigGet sigNat j') (OptionType.some Nat r) -> Eq (OptionType RecRule) (recrule_for renv (genRecName natName sigNat) (ctorName natName j')) (OptionType.some RecRule (RecRule.mk (ctorName natName j') r (genRecRhs natName sigNat u j' r)))) => Nat.rec (fun (j1 : Nat) => forall (r : Nat), Eq (OptionType Nat) (sigGet sigNat (Nat.succ j1)) (OptionType.some Nat r) -> Eq (OptionType RecRule) (recrule_for renv (genRecName natName sigNat) (ctorName natName (Nat.succ j1))) (OptionType.some RecRule (RecRule.mk (ctorName natName (Nat.succ j1)) r (genRecRhs natName sigNat u (Nat.succ j1) r)))) (fun (r : Nat) (hjr : Eq (OptionType Nat) (sigGet sigNat (Nat.succ Nat.zero)) (OptionType.some Nat r)) => Eq.substType Nat (fun (rr : Nat) => Eq (OptionType RecRule) (recrule_for renv (genRecName natName sigNat) (ctorName natName (Nat.succ Nat.zero))) (OptionType.some RecRule (RecRule.mk (ctorName natName (Nat.succ Nat.zero)) rr (genRecRhs natName sigNat u (Nat.succ Nat.zero) rr)))) (Nat.succ Nat.zero) r (option_some_inj Nat (Nat.succ Nat.zero) r hjr) hsucc) (fun (j'' : Nat) (ih2r : forall (r : Nat), Eq (OptionType Nat) (sigGet sigNat (Nat.succ j'')) (OptionType.some Nat r) -> Eq (OptionType RecRule) (recrule_for renv (genRecName natName sigNat) (ctorName natName (Nat.succ j''))) (OptionType.some RecRule (RecRule.mk (ctorName natName (Nat.succ j'')) r (genRecRhs natName sigNat u (Nat.succ j'') r)))) => fun (r : Nat) (hjr : Eq (OptionType Nat) (sigGet sigNat (Nat.succ (Nat.succ j''))) (OptionType.some Nat r)) => option_none_ne_some Nat r (Eq (OptionType RecRule) (recrule_for renv (genRecName natName sigNat) (ctorName natName (Nat.succ (Nat.succ j'')))) (OptionType.some RecRule (RecRule.mk (ctorName natName (Nat.succ (Nat.succ j''))) r (genRecRhs natName sigNat u (Nat.succ (Nat.succ j'')) r)))) hjr) j') j)) hok",
            "NatRecEnvOK u renv -> GenRecEnvOK natName sigNat u renv: concrete Nat recursor-env OK is generic at sig=[0,1] (double Nat.rec; r via option_some_inj; j>=2 vacuous). SnSchema B4b §10a.",
        )?;

        // ── B4c: the λ-telescope calculus (lamTel/instIter/instDomsAt) + the
        // genRecRhs-as-telescope decomposition data (minorTys/replicateLT/
        // genRecDoms). These feed lamTel_beta (the β-chain engine) and
        // genRecRhs_eq_lamTel. Pure ListType.rec/Nat.rec structural defs.
        self.add_recursive_def(
            "def lamTel (doms : ListType KExpr) (body : KExpr) : KExpr := ListType.rec KExpr (fun (_ : ListType KExpr) => KExpr -> KExpr) (fun (b : KExpr) => b) (fun (d : KExpr) (rest : ListType KExpr) (ih : KExpr -> KExpr) => fun (b : KExpr) => KExpr.lam d (ih b)) doms body",
            "lamTel doms body: nest body under one lam per dom (nil->body, cons d rest->lam d (lamTel rest body)). SnSchema B4c.",
        )?;
        self.add_recursive_def(
            "def instIter (body : KExpr) (args : ListType KExpr) : KExpr := ListType.rec KExpr (fun (_ : ListType KExpr) => KExpr -> KExpr) (fun (b : KExpr) => b) (fun (a : KExpr) (rest : ListType KExpr) (ih : KExpr -> KExpr) => fun (b : KExpr) => ih (instantiate_at b a (list_length rest))) args body",
            "instIter body args: iterated instantiate_at (nil->body, cons a rest->instIter (instantiate_at body a (list_length rest)) rest). SnSchema B4c.",
        )?;
        self.add_recursive_def(
            "def instDomsAt (doms : ListType KExpr) (a : KExpr) : Nat -> ListType KExpr := ListType.rec KExpr (fun (_ : ListType KExpr) => Nat -> ListType KExpr) (fun (dep : Nat) => ListType.nil KExpr) (fun (d : KExpr) (rest : ListType KExpr) (ih : Nat -> ListType KExpr) => fun (dep : Nat) => ListType.cons KExpr (instantiate_at d a dep) (ih (Nat.add dep (Nat.succ Nat.zero)))) doms",
            "instDomsAt doms a dep: instantiate_at each dom at increasing depth. SnSchema B4c.",
        )?;
        self.add_recursive_def(
            "def minorTys (fam : Name) (j : Nat) (sig : ListType Nat) : ListType KExpr := ListType.rec Nat (fun (_ : ListType Nat) => Nat -> ListType KExpr) (fun (j0 : Nat) => ListType.nil KExpr) (fun (r : Nat) (rest : ListType Nat) (ih : Nat -> ListType KExpr) => fun (j0 : Nat) => ListType.cons KExpr (minorTy fam j0 r) (ih (Nat.add j0 (Nat.succ Nat.zero)))) sig j",
            "minorTys fam j sig: the list of minor types (minorTy fam j0 r per ctor). SnSchema B4c.",
        )?;
        self.add_recursive_def(
            "def replicateLT (n : Nat) (x : KExpr) : ListType KExpr := Nat.rec (fun (_ : Nat) => ListType KExpr) (ListType.nil KExpr) (fun (n0 : Nat) (ih : ListType KExpr) => ListType.cons KExpr x ih) n",
            "replicateLT n x: a list of n copies of x. SnSchema B4c.",
        )?;
        self.add_recursive_def(
            "def genRecDoms (fam : Name) (sig : ListType Nat) (u : Level) (r : Nat) : ListType KExpr := ListType.cons KExpr (genMotiveTy fam u) (list_append (minorTys fam Nat.zero sig) (replicateLT r (famTypeC fam)))",
            "genRecDoms fam sig u r: the domain telescope of genRecRhs = motive :: minorTys ++ (r field types). SnSchema B4c.",
        )?;

        // ── B4c: the generic one-step / multi-step reduction relation over
        // genREnv — the (fam, sig, u)-parametrized clone of natrec.rs's
        // iotaCong/natStep/natSteps (which are hardwired to natREnv). This is the
        // target relation of genRecContract_steps. Placed here (objects stage,
        // before the CandModel stage) so B5 can reference genSteps.
        self.add_inductive(
            "inductive genIotaCong (fam : Name) (sig : ListType Nat) (u : Level) : KExpr -> KExpr -> Type\n| head : forall (e : KExpr) (e2 : KExpr), iota_step (genREnv fam sig u) e e2 -> genIotaCong fam sig u e e2\n| app_left : forall (f : KExpr) (f2 : KExpr) (a : KExpr), genIotaCong fam sig u f f2 -> genIotaCong fam sig u (KExpr.app f a) (KExpr.app f2 a)\n| app_right : forall (f : KExpr) (a : KExpr) (a2 : KExpr), genIotaCong fam sig u a a2 -> genIotaCong fam sig u (KExpr.app f a) (KExpr.app f a2)",
            "genIotaCong fam sig u e e2: one-hole congruence closure of object-level iota over genREnv. Generalizes iotaCong. SnSchema B4c.",
        )?;
        self.add_inductive(
            "inductive genStep (fam : Name) (sig : ListType Nat) (u : Level) : KExpr -> KExpr -> Type\n| iota : forall (e : KExpr) (e2 : KExpr), genIotaCong fam sig u e e2 -> genStep fam sig u e e2\n| beta : forall (e : KExpr) (e2 : KExpr), beta_reduces e e2 -> genStep fam sig u e e2",
            "genStep fam sig u e e2: one generic-recursor weak-head step — object-level iota (congruent) over genREnv, or a beta/congruence step. Generalizes natStep. SnSchema B4c.",
        )?;
        self.add_inductive(
            "inductive genSteps (fam : Name) (sig : ListType Nat) (u : Level) : KExpr -> KExpr -> Type\n| refl : forall (e : KExpr), genSteps fam sig u e e\n| step : forall (e : KExpr) (e2 : KExpr) (e3 : KExpr), genStep fam sig u e e2 -> genSteps fam sig u e2 e3 -> genSteps fam sig u e e3",
            "genSteps fam sig u e e2: reflexive-transitive closure of genStep. Generalizes natSteps. SnSchema B4c.",
        )?;

        // Step-relation congruence + transitivity helpers (clones of
        // natrec.rs:360/387/392 with fam/sig/u params).
        self.add_recursive_def(
            "def genSteps_trans (fam : Name) (sig : ListType Nat) (u : Level) (a : KExpr) (b : KExpr) (c : KExpr) (h1 : genSteps fam sig u a b) (h2 : genSteps fam sig u b c) : genSteps fam sig u a c := genSteps.rec fam sig u (fun (a0 : KExpr) (b0 : KExpr) (_ : genSteps fam sig u a0 b0) => genSteps fam sig u b0 c -> genSteps fam sig u a0 c) (fun (e : KExpr) => fun (hc : genSteps fam sig u e c) => hc) (fun (e : KExpr) (e2 : KExpr) (e3 : KExpr) (st : genStep fam sig u e e2) (_rest : genSteps fam sig u e2 e3) (ih : genSteps fam sig u e3 c -> genSteps fam sig u e2 c) => fun (hc : genSteps fam sig u e3 c) => genSteps.step fam sig u e e2 c st (ih hc)) a b h1 h2",
            "genSteps transitivity (genSteps.rec on h1). SnSchema B4c.",
        )?;
        self.add_recursive_def(
            "def genStep_app_right (fam : Name) (sig : ListType Nat) (u : Level) (f : KExpr) (e : KExpr) (e2 : KExpr) (h : genStep fam sig u e e2) : genStep fam sig u (KExpr.app f e) (KExpr.app f e2) := match h with\n| genStep.iota ic => genStep.iota fam sig u (KExpr.app f e) (KExpr.app f e2) (genIotaCong.app_right fam sig u f e e2 ic)\n| genStep.beta br => genStep.beta fam sig u (KExpr.app f e) (KExpr.app f e2) (beta_reduces.app_right f e e2 br)",
            "genStep congruence under app-right (match on the step). SnSchema B4c.",
        )?;
        self.add_recursive_def(
            "def genSteps_app_right (fam : Name) (sig : ListType Nat) (u : Level) (f : KExpr) (a : KExpr) (b : KExpr) (h : genSteps fam sig u a b) : genSteps fam sig u (KExpr.app f a) (KExpr.app f b) := genSteps.rec fam sig u (fun (a0 : KExpr) (b0 : KExpr) (_ : genSteps fam sig u a0 b0) => genSteps fam sig u (KExpr.app f a0) (KExpr.app f b0)) (fun (e : KExpr) => genSteps.refl fam sig u (KExpr.app f e)) (fun (e : KExpr) (e2 : KExpr) (e3 : KExpr) (st : genStep fam sig u e e2) (_rest : genSteps fam sig u e2 e3) (ih : genSteps fam sig u (KExpr.app f e2) (KExpr.app f e3)) => genSteps.step fam sig u (KExpr.app f e) (KExpr.app f e2) (KExpr.app f e3) (genStep_app_right fam sig u f e e2 st) ih) a b h",
            "genSteps congruence under app-right (genSteps.rec on h). SnSchema B4c.",
        )?;

        // ── INDEXED-INDUCTIVE OBJECT LAYER (Idx lane, tranche 1) ───────────
        //
        // Before this, the spec had only `ICtor` + its projections; the indexed
        // recursor had no object layer at all, which is why the port draft
        // listed redRecIdx as fully BLOCKED. This lands the layer: the recursor
        // spine, rules, environment, contract and gates, each mirroring a named
        // existing gen* declaration.
        //
        // Ported from the Aristotle guide
        // scratch/aristotle-harvest/U-aristotle-idx-adequacy/.../IndexedAdequacy.lean
        // (sorry-free, elaborates under the pinned toolchain).
        //
        // The trailing `*_nat*` declarations are spec-only rfl FIXTURES with no
        // guide analogue: they pin the indexed constructions against the
        // already-checked Nat ones at nIdx = 0, in the same style as
        // genRecApp_nat / genREnv_nat / genRecRhs_nat_succ. iREnv_nat is the
        // whole-assembly gate — it validates iREnv + iRecMeta + iRecRules +
        // iRecRulesFrom + iRecRhs + iRecDoms + iFieldDoms + iRecRhsBody +
        // iRecCallsB + iRecC simultaneously against natREnv.
        self.add_recursive_def(
            "def isigGet (isig : ListType ICtor) (j : Nat) : OptionType ICtor := ListType.rec ICtor (fun (_ : ListType ICtor) => Nat -> OptionType ICtor) (fun (j0 : Nat) => OptionType.none ICtor) (fun (d : ICtor) (rest : ListType ICtor) (ih : Nat -> OptionType ICtor) => fun (j0 : Nat) => Nat.rec (fun (_ : Nat) => OptionType ICtor) (OptionType.some ICtor d) (fun (j1 : Nat) (_ : OptionType ICtor) => ih j1) j0) isig j",
            "isigGet: indexed-inductive object layer. Guide IndexedAdequacy.lean:461 (isigGet); spec shape mirror = sigGet at schema.rs:529.",
        )?;

        self.add_recursive_def(
            "def iRecC (fam : Name) (isig : ListType ICtor) (u : Level) : KExpr := KExpr.const (iRecName fam isig) (ListType.cons Level u (ListType.nil Level))",
            "iRecC: indexed-inductive object layer. Guide IndexedAdequacy.lean:499 (iRecC); spec shape mirror = genRecC at schema.rs:95; iRecName already exists at schema.rs:421.",
        )?;

        self.add_recursive_def(
            "def instVec (iv : ListType KExpr) (args : ListType KExpr) : ListType KExpr := mapLT (fun (e : KExpr) => instIter e args) iv",
            "instVec: indexed-inductive object layer. Guide IndexedAdequacy.lean:477 (instVec); mapLT schema.rs:346, instIter schema.rs:632. Guide's ofList/ofList_length (:467,:471) DROP OUT: spec ICtor already stores ListType KExpr, not Lean List.",
        )?;

        self.add_recursive_def(
            "def iFieldDoms (fam : Name) (i : Nat) (recs : ListType (ListType KExpr)) : ListType KExpr := ListType.rec (ListType KExpr) (fun (_ : ListType (ListType KExpr)) => Nat -> ListType KExpr) (fun (i0 : Nat) => ListType.nil KExpr) (fun (iv : ListType KExpr) (rest : ListType (ListType KExpr)) (ih : Nat -> ListType KExpr) => fun (i0 : Nat) => ListType.cons KExpr (famAppI fam (mapLT (fun (e : KExpr) => lift_at e Nat.zero i0) iv)) (ih (Nat.add i0 (Nat.succ Nat.zero)))) recs i",
            "iFieldDoms: indexed-inductive object layer. Guide IndexedAdequacy.lean:552 (iFieldDoms); the list-valued twin of the ALREADY-CHECKED iFieldTel at schema.rs:370 — same recursion, same i-threading, ListType.cons instead of KExpr.pi.",
        )?;

        self.add_recursive_def(
            "def iRecDoms (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) (d : ICtor) : ListType KExpr := ListType.cons KExpr (iMotiveTy iFam fam nIdx u) (list_append (iMinorTys iFam fam Nat.zero isig) (list_append (replicateLT (icP d) (famTypeC iFam)) (iFieldDoms fam Nat.zero (icRecs d))))",
            "iRecDoms: indexed-inductive object layer. Guide IndexedAdequacy.lean:558 (iRecDoms); spec shape mirror = genRecDoms schema.rs:648. iMotiveTy :253, iMinorTys :399, replicateLT :644 (arg order n then x — matches guide).",
        )?;

        self.add_recursive_def(
            "def iRecCallsB (fam : Name) (isig : ListType ICtor) (u : Level) (p : Nat) (r : Nat) (k : Nat) (i : Nat) (recs : ListType (ListType KExpr)) : ListType KExpr := ListType.rec (ListType KExpr) (fun (_ : ListType (ListType KExpr)) => Nat -> ListType KExpr) (fun (i0 : Nat) => ListType.nil KExpr) (fun (iv : ListType KExpr) (rest : ListType (ListType KExpr)) (ih : Nat -> ListType KExpr) => fun (i0 : Nat) => ListType.cons KExpr (apply_spine (list_append (bvarSeq (Nat.add (Nat.add p r) k) (Nat.add k (Nat.succ Nat.zero))) (list_append (mapLT (fun (e : KExpr) => lift_at e Nat.zero r) iv) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) i0)) (ListType.nil KExpr)))) (iRecC fam isig u)) (ih (Nat.add i0 (Nat.succ Nat.zero)))) recs i",
            "iRecCallsB: indexed-inductive object layer. Guide IndexedAdequacy.lean:566 (iRecCallsB). NO spec analogue — genRecRhsBody (schema.rs:361) inlines its rec-calls via mapLT. This is one of the two hard de Bruijn decls; gated by iRecRhsBody_nat_succ below.",
        )?;

        self.add_recursive_def(
            "def iRecRhsBody (fam : Name) (isig : ListType ICtor) (u : Level) (j : Nat) (d : ICtor) : KExpr := apply_spine (list_append (bvarSeq (Nat.sub (Nat.add (icP d) (recsLen (icRecs d))) (Nat.succ Nat.zero)) (Nat.add (icP d) (recsLen (icRecs d)))) (iRecCallsB fam isig u (icP d) (recsLen (icRecs d)) (iSigLength isig) Nat.zero (icRecs d))) (KExpr.bvar (Nat.add (Nat.add (icP d) (recsLen (icRecs d))) (Nat.sub (Nat.sub (iSigLength isig) (Nat.succ Nat.zero)) j)))",
            "iRecRhsBody: indexed-inductive object layer. Guide IndexedAdequacy.lean:579 (iRecRhsBody); spec shape mirror = genRecRhsBody schema.rs:361. THE hardest de Bruijn in the tranche; hand-reduced against genRecRhsBody at p=0 and found term-identical (see blocking_gaps).",
        )?;

        self.add_recursive_def(
            "def iRecRhs (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) (j : Nat) (d : ICtor) : KExpr := lamTel (iRecDoms iFam fam nIdx isig u d) (iRecRhsBody fam isig u j d)",
            "iRecRhs: indexed-inductive object layer. Guide IndexedAdequacy.lean:586 (iRecRhs). Guide authors DIRECTLY as lamTel (spec lamTel schema.rs:628), deliberately skipping the spec's genRecRhs/genRecRhs_eq_lamTel two-step (schema.rs:474 / :1053) — guide authoring kept.",
        )?;

        self.add_recursive_def(
            "def iRecMeta (nIdx : Nat) (isig : ListType ICtor) : RecMeta := RecMeta.mk Nat.zero (Nat.succ Nat.zero) (iSigLength isig) nIdx Bool.true",
            "iRecMeta: indexed-inductive object layer. Guide IndexedAdequacy.lean:605 (iRecMeta); spec shape mirror = genRecMeta schema.rs:107. FIRST RecMeta in the spec with num_indices != 0 (genRecMeta/natRecMeta both pass Nat.zero).",
        )?;

        self.add_recursive_def(
            "def iRecRulesFrom (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) (j : Nat) (rest : ListType ICtor) : RecRules := ListType.rec ICtor (fun (_ : ListType ICtor) => Nat -> RecRules) (fun (j0 : Nat) => RecRules.nil) (fun (d : ICtor) (rest0 : ListType ICtor) (ih : Nat -> RecRules) => fun (j0 : Nat) => RecRules.cons (RecRule.mk (ctorName fam j0) (Nat.add (icP d) (recsLen (icRecs d))) (iRecRhs iFam fam nIdx isig u j0 d)) (ih (Nat.add j0 (Nat.succ Nat.zero)))) rest j",
            "iRecRulesFrom: indexed-inductive object layer. Guide IndexedAdequacy.lean:591 (iRecRulesFrom); spec shape mirror = genRecRulesFrom schema.rs:480. RecRule.mk = (ctor_name, num_fields, rhs) per rec_env.rs:102; num_fields = p + r.",
        )?;

        self.add_recursive_def(
            "def iRecRules (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) : RecRules := iRecRulesFrom iFam fam nIdx isig u Nat.zero isig",
            "iRecRules: indexed-inductive object layer. Guide IndexedAdequacy.lean:600 (iRecRules); spec shape mirror = genRecRules schema.rs:484.",
        )?;

        self.add_recursive_def(
            "def iREnv (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) : RecEnv := RecEnv.addRec RecEnv.empty (iRecName fam isig) (iRecMeta nIdx isig) (iRecRules iFam fam nIdx isig u)",
            "iREnv: indexed-inductive object layer. Guide IndexedAdequacy.lean:608 (iREnv); spec shape mirror = genREnv schema.rs:489; RecEnv.addRec arg order per rec_env.rs:134.",
        )?;

        self.add_recursive_def(
            "def iRecApp (fam : Name) (isig : ListType ICtor) (u : Level) (m : KExpr) (ms : ListType KExpr) (ix : ListType KExpr) (t : KExpr) : KExpr := apply_spine (ListType.cons KExpr m (list_append ms (list_append ix (ListType.cons KExpr t (ListType.nil KExpr))))) (iRecC fam isig u)",
            "iRecApp: indexed-inductive object layer. Guide IndexedAdequacy.lean:614 (iRecApp); spec shape mirror = genRecApp schema.rs:495 plus the index vector between minors and major.",
        )?;

        self.add_recursive_def(
            "def iRecCallsInst (fam : Name) (isig : ListType ICtor) (u : Level) (m : KExpr) (ms : ListType KExpr) (avec : ListType KExpr) (recs : ListType (ListType KExpr)) (fields : ListType KExpr) : ListType KExpr := ListType.rec (ListType KExpr) (fun (_ : ListType (ListType KExpr)) => ListType KExpr -> ListType KExpr) (fun (fs : ListType KExpr) => ListType.nil KExpr) (fun (iv : ListType KExpr) (rest : ListType (ListType KExpr)) (ih : ListType KExpr -> ListType KExpr) => fun (fs : ListType KExpr) => ListType.rec KExpr (fun (_ : ListType KExpr) => ListType KExpr) (ListType.nil KExpr) (fun (f : KExpr) (fs0 : ListType KExpr) (_ : ListType KExpr) => ListType.cons KExpr (iRecApp fam isig u m ms (instVec iv avec) f) (ih fs0)) fs) recs fields",
            "iRecCallsInst: indexed-inductive object layer. Guide IndexedAdequacy.lean:621 (iRecCallsInst). Guide's 3 pattern clauses realized as nested ListType.rec (outer on recs returning ListType KExpr -> ListType KExpr, inner on fields): recs=nil -> nil regardless of fields (guide clauses 1+2); cons/nil -> nil (clause 1); cons/cons -> cons (clause 3).",
        )?;

        self.add_recursive_def(
            "def iContractum (fam : Name) (isig : ListType ICtor) (u : Level) (m : KExpr) (mj : KExpr) (ms : ListType KExpr) (avec : ListType KExpr) (fields : ListType KExpr) (d : ICtor) : KExpr := apply_spine (list_append avec (list_append fields (iRecCallsInst fam isig u m ms avec (icRecs d) fields))) mj",
            "iContractum: indexed-inductive object layer. Guide IndexedAdequacy.lean:631 (iContractum); spec shape mirror = genContractum schema.rs:541. Guide param order kept (m mj ms as fields d) with `as` renamed `avec`.",
        )?;

        self.add_inductive(
            "inductive IGenRecContract (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) : KExpr -> KExpr -> Type\n| rule : forall (j : Nat) (d : ICtor) (m : KExpr) (mj : KExpr) (ms : ListType KExpr) (ix : ListType KExpr) (avec : ListType KExpr) (fields : ListType KExpr), Eq (OptionType ICtor) (isigGet isig j) (OptionType.some ICtor d) -> Eq Nat (list_length ms) (iSigLength isig) -> Eq (OptionType KExpr) (listGet ms j) (OptionType.some KExpr mj) -> Eq Nat (list_length ix) nIdx -> Eq Nat (list_length avec) (icP d) -> Eq Nat (list_length fields) (recsLen (icRecs d)) -> IGenRecContract fam nIdx isig u (iRecApp fam isig u m ms ix (ctorApp fam j (list_append avec fields))) (iContractum fam isig u m mj ms avec fields d)",
            "IGenRecContract: indexed-inductive object layer. Guide IndexedAdequacy.lean:640 (IGenRecContract); spec shape mirror = GenRecContract schema.rs:550 (Type-valued, Eq-hypothesis idiom instead of Prop =). listGet schema.rs:534, list_length iota_step.rs:101.",
        )?;

        self.add_inductive(
            "inductive IGenFresh (fam : Name) (isig : ListType ICtor) : DefEnv -> Type\n| mk : forall (denv : DefEnv), Eq (OptionType KExpr) (defval_for denv fam) (OptionType.none KExpr) -> (forall (j : Nat), Lt j (iSigLength isig) -> Eq (OptionType KExpr) (defval_for denv (ctorName fam j)) (OptionType.none KExpr)) -> Eq (OptionType KExpr) (defval_for denv (iRecName fam isig)) (OptionType.none KExpr) -> IGenFresh fam isig denv",
            "IGenFresh: indexed-inductive object layer. Guide IndexedAdequacy.lean:654 (IGenFresh); spec shape mirror = GenFresh schema.rs:556. Guide's `j < isig.length` becomes the spec idiom `Lt j (iSigLength isig)` (Lt: foundation_types.rs:646); defval_for: delta_step.rs:50.",
        )?;

        self.add_inductive(
            "inductive IGenRecEnvOK (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) : RecEnv -> Type\n| mk : forall (renv : RecEnv), Eq (OptionType RecMeta) (recmeta_for renv (iRecName fam isig)) (OptionType.some RecMeta (iRecMeta nIdx isig)) -> (forall (j : Nat) (d : ICtor), Eq (OptionType ICtor) (isigGet isig j) (OptionType.some ICtor d) -> Eq (OptionType RecRule) (recrule_for renv (iRecName fam isig) (ctorName fam j)) (OptionType.some RecRule (RecRule.mk (ctorName fam j) (Nat.add (icP d) (recsLen (icRecs d))) (iRecRhs iFam fam nIdx isig u j d)))) -> IGenRecEnvOK iFam fam nIdx isig u renv",
            "IGenRecEnvOK: indexed-inductive object layer. Guide IndexedAdequacy.lean:660 (IGenRecEnvOK); spec shape mirror = GenRecEnvOK schema.rs:562. recmeta_for rec_env.rs:238, recrule_for rec_env.rs:255.",
        )?;

        self.add_recursive_def(
            "def idNatZero : ICtor := ICtor.mk Nat.zero (ListType.nil (ListType KExpr)) (ListType.nil KExpr)",
            "idNatZero: indexed-inductive object layer. Guide No guide analogue — spec-only degeneracy fixture. Mirrors the sigNat=[0,1] convention of schema.rs:60 lifted to ICtor: p=0, no rec fields, empty target vector (nIdx=0).",
        )?;

        self.add_recursive_def(
            "def idNatSucc : ICtor := ICtor.mk Nat.zero (ListType.cons (ListType KExpr) (ListType.nil KExpr) (ListType.nil (ListType KExpr))) (ListType.nil KExpr)",
            "idNatSucc: indexed-inductive object layer. Guide No guide analogue — spec-only degeneracy fixture: p=0, ONE recursive field with an empty index vector, empty target vector. ICtor.mk arg order per schema.rs:269/:450.",
        )?;

        self.add_recursive_def(
            "def isigNat : ListType ICtor := ListType.cons ICtor idNatZero (ListType.cons ICtor idNatSucc (ListType.nil ICtor))",
            "isigNat: indexed-inductive object layer. Guide No guide analogue — spec-only. The nIdx=0 indexed re-encoding of sigNat (schema.rs:60); iSigLength isigNat reduces to 2, matching sigLength sigNat.",
        )?;

        self.add_recursive_def(
            "def instVec_nat_id : Eq (ListType KExpr) (instVec (ListType.cons KExpr (KExpr.bvar (Nat.succ Nat.zero)) (ListType.cons KExpr (KExpr.bvar Nat.zero) (ListType.nil KExpr))) (ListType.cons KExpr natZeroC (ListType.cons KExpr natTypeC (ListType.nil KExpr)))) (ListType.cons KExpr natZeroC (ListType.cons KExpr natTypeC (ListType.nil KExpr))) := Eq.refl (ListType KExpr) (ListType.cons KExpr natZeroC (ListType.cons KExpr natTypeC (ListType.nil KExpr)))",
            "instVec_nat_id: indexed-inductive object layer. Guide No guide analogue (guide validates instVec only via instVec_length :480, which needs LATE-stage mapLT_length). Spec-only rfl: instVec [bvar 1, bvar 0] [natZeroC, natTypeC] = [natZeroC, natTypeC] — validates instIter's arg ORDER and its list_length-rest DEPTH threading. Both values are KExpr.const (natrec.rs:69,:73) so lift_at reduces (expr_model.rs:92).",
        )?;

        self.add_recursive_def(
            "def iRecDoms_nat_succ (u : Level) : Eq (ListType KExpr) (iRecDoms natName natName Nat.zero isigNat u idNatSucc) (genRecDoms natName sigNat u (Nat.succ Nat.zero)) := Eq.refl (ListType KExpr) (genRecDoms natName sigNat u (Nat.succ Nat.zero))",
            "iRecDoms_nat_succ: indexed-inductive object layer. Guide No guide analogue — spec-only rfl, the exact precedent-shape of iMotiveTy_deg (schema.rs:260) and genRecTy_nat (:224). Validates iRecDoms + iFieldDoms + (iMinorTys/iMinorTy degenerating to minorTys/minorTy).",
        )?;

        self.add_recursive_def(
            "def iRecRhsBody_nat_zero (u : Level) : Eq KExpr (iRecRhsBody natName isigNat u Nat.zero idNatZero) (genRecRhsBody natName sigNat u Nat.zero Nat.zero) := Eq.refl KExpr (genRecRhsBody natName sigNat u Nat.zero Nat.zero)",
            "iRecRhsBody_nat_zero: indexed-inductive object layer. Guide No guide analogue — spec-only rfl in the precedent class of genRecRhs_nat_zero (schema.rs:501). Both sides reduce to KExpr.bvar 1.",
        )?;

        self.add_recursive_def(
            "def iRecRhsBody_nat_succ (u : Level) : Eq KExpr (iRecRhsBody natName isigNat u (Nat.succ Nat.zero) idNatSucc) (genRecRhsBody natName sigNat u (Nat.succ Nat.zero) (Nat.succ Nat.zero)) := Eq.refl KExpr (genRecRhsBody natName sigNat u (Nat.succ Nat.zero) (Nat.succ Nat.zero))",
            "iRecRhsBody_nat_succ: indexed-inductive object layer. Guide No guide analogue — spec-only rfl, the direct analogue of genRecRhs_nat_succ (schema.rs:505), which the file itself calls 'the HARDEST de Bruijn validation'. THIS IS THE TRANCHE GATE for iRecCallsB + iRecRhsBody.",
        )?;

        self.add_recursive_def(
            "def iRecApp_nat (u : Level) (m : KExpr) (ms : ListType KExpr) (t : KExpr) : Eq KExpr (iRecApp natName isigNat u m ms (ListType.nil KExpr) t) (genRecApp natName sigNat u m ms t) := Eq.refl KExpr (genRecApp natName sigNat u m ms t)",
            "iRecApp_nat: indexed-inductive object layer. Guide No guide analogue — spec-only rfl in the class of genRecApp_nat (schema.rs:517). Holds for ARBITRARY m/ms/t: list_append nil [t] reduces, and iRecC/genRecC heads both reduce to const (Name.str natName 2) [u].",
        )?;

        self.add_recursive_def(
            "def iContractum_nat_succ (u : Level) (m : KExpr) (mj : KExpr) (ms : ListType KExpr) (f : KExpr) : Eq KExpr (iContractum natName isigNat u m mj ms (ListType.nil KExpr) (ListType.cons KExpr f (ListType.nil KExpr)) idNatSucc) (genContractum natName sigNat u m ms mj (ListType.cons KExpr f (ListType.nil KExpr))) := Eq.refl KExpr (genContractum natName sigNat u m ms mj (ListType.cons KExpr f (ListType.nil KExpr)))",
            "iContractum_nat_succ: indexed-inductive object layer. Guide No guide analogue — spec-only rfl. Validates iRecCallsInst's LOCKSTEP recursion against genContractum's mapLT (schema.rs:541) at the one-rec-field instance. NOTE genContractum's arg order is (m ms mj fields), iContractum's is (m mj ms avec fields d).",
        )?;

        self.add_recursive_def(
            "def iREnv_nat (u : Level) : Eq RecEnv (iREnv natName natName Nat.zero isigNat u) (natREnv u) := Eq.refl RecEnv (natREnv u)",
            "iREnv_nat: indexed-inductive object layer. Guide No guide analogue — spec-only rfl, the analogue of genREnv_nat (schema.rs:513). WHOLE-ASSEMBLY gate: one decl validates iREnv + iRecMeta + iRecRules + iRecRulesFrom + iRecRhs + iRecDoms + iFieldDoms + iRecRhsBody + iRecCallsB + iRecC simultaneously against natREnv (natrec.rs:134).",
        )?;

        Ok(())
    }

    /// SnSchema LEMMA half (Brick 4b+): the env-lookup lemmas (genREnv_meta_rec /
    /// genRecRules_lookup / genREnv_ok), the object-level iota realization
    /// (genRecContract_steps), and the §10a' Nat→Gen bridges. Kept AFTER
    /// add_natrec (needs name_eqb_refl from kexpr_beq + the psubst β-chain from
    /// add_dependent_sn_richmodel + the Nat contract/steps machinery).
    pub(super) fn add_snschema(&mut self) -> Result<(), SpecError> {
        // ── Name/Nat equality reflexivity (re-derived here: kexpr_beq's
        // name_eqb_refl/nat_eqb_refl are NOT wired into the shared STAGES spec —
        // add_kexpr_beq runs only in its own test build). Needed because
        // name_eqb (genRecName fam sig) (genRecName fam sig) is STUCK for
        // abstract fam (unlike the concrete Nat names, which reduce by rfl).
        // Foundational closure (Eq.cong/Name.rec), census-neutral.
        self.add_recursive_def(
            "def nat_eqb_refl (n : Nat) : Eq Bool (nat_eqb n n) Bool.true := Eq.cong Nat Bool (fun (s : Nat) => nat_is_zero (Nat.add s s)) (Nat.sub n n) Nat.zero (nat_sub_self n)",
            "nat_eqb n n = true (Eq.cong transport of nat_sub_self). SnSchema B4b (re-derived).",
        )?;

        self.add_recursive_def(
            "def name_eqb_refl (m : Name) : Eq Bool (name_eqb m m) Bool.true := Name.rec (fun (z : Name) => Eq Bool (name_eqb z z) Bool.true) (Eq.refl Bool Bool.true) (fun (p : Name) (k : Nat) (ih : Eq Bool (name_eqb p p) Bool.true) => Eq.trans Bool (name_eqb (Name.str p k) (Name.str p k)) (Bool.and Bool.true (nat_eqb k k)) Bool.true (Eq.cong Bool Bool (fun (bp : Bool) => Bool.and bp (nat_eqb k k)) (name_eqb p p) Bool.true ih) (nat_eqb_refl k)) m",
            "name_eqb m m = true (Name.rec induction + nat_eqb_refl). SnSchema B4b (re-derived).",
        )?;

        // ── B4b: env lookups. genREnv_meta_rec — the recursor's OWN name finds
        // its metadata in genREnv (name_eqb_refl on the recursor name; opt_pick
        // true reduces to some by rfl).
        self.add_recursive_def(
            "def genREnv_meta_rec (fam : Name) (sig : ListType Nat) (u : Level) : Eq (OptionType RecMeta) (recmeta_for (genREnv fam sig u) (genRecName fam sig)) (OptionType.some RecMeta (genRecMeta sig)) := Eq.substType Bool (fun (b : Bool) => Eq (OptionType RecMeta) (opt_pick RecMeta b (genRecMeta sig) (OptionType.none RecMeta)) (OptionType.some RecMeta (genRecMeta sig))) Bool.true (name_eqb (genRecName fam sig) (genRecName fam sig)) (Eq.symm Bool (name_eqb (genRecName fam sig) (genRecName fam sig)) Bool.true (name_eqb_refl (genRecName fam sig))) (Eq.refl (OptionType RecMeta) (OptionType.some RecMeta (genRecMeta sig)))",
            "genREnv carries the recursor's metadata (name_eqb_refl on genRecName). SnSchema B4b.",
        )?;

        // ── B4b: nat inequality toolbox for the ctor-name lookup mismatch case.
        // The generic recursor-rules lookup must show `ctorName fam j0` ≠
        // `ctorName fam (j0 + succ j)` — i.e. `nat_eqb j0 (Nat.add j0 (Nat.succ
        // j)) = false`. nat_eqb a b = nat_is_zero (Nat.add (Nat.sub a b)
        // (Nat.sub b a)); the two auxiliary sub-cancellation lemmas make the
        // right summand succ-headed and the left summand zero. All foundational
        // (Nat.rec + nat_sub_succ_succ/nat_succ_add/nat_zero_add/nat_sub_zero_*).

        // Nat.sub (Nat.add a c) a = c — the added part survives cancellation.
        // Induct on a: base uses nat_sub_zero_right + nat_zero_add; step rewrites
        // Nat.add (succ p) c ↦ succ (Nat.add p c) (nat_succ_add), strips the
        // shared successor (nat_sub_succ_succ), then applies the IH.
        self.add_recursive_def(
            "def nat_sub_add_left_cancel (a : Nat) (c : Nat) : Eq Nat (Nat.sub (Nat.add a c) a) c := Nat.rec (fun (k : Nat) => Eq Nat (Nat.sub (Nat.add k c) k) c) (Eq.trans Nat (Nat.sub (Nat.add Nat.zero c) Nat.zero) (Nat.add Nat.zero c) c (nat_sub_zero_right (Nat.add Nat.zero c)) (nat_zero_add c)) (fun (p : Nat) (ih : Eq Nat (Nat.sub (Nat.add p c) p) c) => Eq.trans Nat (Nat.sub (Nat.add (Nat.succ p) c) (Nat.succ p)) (Nat.sub (Nat.add p c) p) c (Eq.trans Nat (Nat.sub (Nat.add (Nat.succ p) c) (Nat.succ p)) (Nat.sub (Nat.succ (Nat.add p c)) (Nat.succ p)) (Nat.sub (Nat.add p c) p) (Eq.cong Nat Nat (fun (y : Nat) => Nat.sub y (Nat.succ p)) (Nat.add (Nat.succ p) c) (Nat.succ (Nat.add p c)) (nat_succ_add p c)) (nat_sub_succ_succ (Nat.add p c) p)) ih) a",
            "Nat.sub (Nat.add a c) a = c (Nat.rec on a; nat_succ_add + nat_sub_succ_succ). SnSchema B4b.",
        )?;

        // Nat.sub a (Nat.add a c) = 0 — subtracting a ≥-quantity gives zero.
        // Induct on a: base uses nat_sub_zero_left; step rewrites the subtrahend
        // Nat.add (succ p) c ↦ succ (Nat.add p c) (nat_succ_add), strips the
        // shared successor (nat_sub_succ_succ), then applies the IH.
        self.add_recursive_def(
            "def nat_sub_self_add_zero (a : Nat) (c : Nat) : Eq Nat (Nat.sub a (Nat.add a c)) Nat.zero := Nat.rec (fun (k : Nat) => Eq Nat (Nat.sub k (Nat.add k c)) Nat.zero) (nat_sub_zero_left (Nat.add Nat.zero c)) (fun (p : Nat) (ih : Eq Nat (Nat.sub p (Nat.add p c)) Nat.zero) => Eq.trans Nat (Nat.sub (Nat.succ p) (Nat.add (Nat.succ p) c)) (Nat.sub p (Nat.add p c)) Nat.zero (Eq.trans Nat (Nat.sub (Nat.succ p) (Nat.add (Nat.succ p) c)) (Nat.sub (Nat.succ p) (Nat.succ (Nat.add p c))) (Nat.sub p (Nat.add p c)) (Eq.cong Nat Nat (fun (y : Nat) => Nat.sub (Nat.succ p) y) (Nat.add (Nat.succ p) c) (Nat.succ (Nat.add p c)) (nat_succ_add p c)) (nat_sub_succ_succ p (Nat.add p c))) ih) a",
            "Nat.sub a (Nat.add a c) = 0 (Nat.rec on a; nat_succ_add + nat_sub_succ_succ). SnSchema B4b.",
        )?;

        // nat_eqb j0 (Nat.add j0 (Nat.succ j)) = false — the ctor-name distinctness
        // needed by genRecRulesFrom_lookup's mismatch case. Rewrites the two
        // subtractions inside nat_eqb: left ↦ 0 (nat_sub_self_add_zero), right ↦
        // succ b (nat_sub_add_left_cancel); then nat_is_zero (Nat.add 0 (succ b))
        // = false by rfl (Nat.add x (succ _) is succ-headed, nat_is_zero succ = false).
        self.add_recursive_def(
            "def nat_eqb_self_add_succ_false (a : Nat) (b : Nat) : Eq Bool (nat_eqb a (Nat.add a (Nat.succ b))) Bool.false := Eq.trans Bool (nat_eqb a (Nat.add a (Nat.succ b))) (nat_is_zero (Nat.add Nat.zero (Nat.succ b))) Bool.false (Eq.cong Nat Bool nat_is_zero (Nat.add (Nat.sub a (Nat.add a (Nat.succ b))) (Nat.sub (Nat.add a (Nat.succ b)) a)) (Nat.add Nat.zero (Nat.succ b)) (Eq.trans Nat (Nat.add (Nat.sub a (Nat.add a (Nat.succ b))) (Nat.sub (Nat.add a (Nat.succ b)) a)) (Nat.add Nat.zero (Nat.sub (Nat.add a (Nat.succ b)) a)) (Nat.add Nat.zero (Nat.succ b)) (Eq.cong Nat Nat (fun (y : Nat) => Nat.add y (Nat.sub (Nat.add a (Nat.succ b)) a)) (Nat.sub a (Nat.add a (Nat.succ b))) Nat.zero (nat_sub_self_add_zero a (Nat.succ b))) (Eq.cong Nat Nat (fun (y : Nat) => Nat.add Nat.zero y) (Nat.sub (Nat.add a (Nat.succ b)) a) (Nat.succ b) (nat_sub_add_left_cancel a (Nat.succ b))))) (Eq.refl Bool Bool.false)",
            "nat_eqb a (Nat.add a (Nat.succ b)) = false (sub-cancel rewrites + succ-headed rfl). SnSchema B4b.",
        )?;

        // ── B4b: the recursor-rules lookup. Looking up ctor (jb+jo) in the rule
        // list `genRecRulesFrom fam sig u jb rest` returns exactly its rule iff
        // `sigGet rest jo = some rv`. Proven by ListType.rec on `rest` with jb/jo/
        // rv/hyp generalized into the motive:
        //   • nil  → sigGet nil jo = none, hypothesis absurd (option_none_ne_some).
        //   • cons → Nat.rec case-split on the offset jo (hypothesis folded into
        //     the split motive):
        //       – jo = 0     : name_eqb (ctorName fam jb) (ctorName fam jb) = true
        //         (name_eqb_refl), opt_pick fires to the head rule; rh = rv by
        //         option_some_inj, transported by Eq.cong.
        //       – jo = succ  : name_eqb (ctorName fam jb) (ctorName fam (jb+succ jp))
        //         = false (name_eqb_refl on fam + nat_eqb_self_add_succ_false),
        //         opt_pick falls through to the tail; the outer IH at start jb+1
        //         discharges it, index-shifted by nat_succ_add.
        // Foundational throughout (recursors + the nat/name equality lemmas).
        self.add_recursive_def(
            concat!(
                "def genRecRulesFrom_lookup (fam : Name) (sig : ListType Nat) (u : Level) (j0 : Nat) (rest : ListType Nat) (j : Nat) (r : Nat) ",
                "(hjr : Eq (OptionType Nat) (sigGet rest j) (OptionType.some Nat r)) ",
                ": Eq (OptionType RecRule) (recrule_in_rules (genRecRulesFrom fam sig u j0 rest) (ctorName fam (Nat.add j0 j))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add j0 j)) r (genRecRhs fam sig u (Nat.add j0 j) r))) := ",
                "ListType.rec Nat ",
                // MOTIVE
                "(fun (rst : ListType Nat) => forall (jb : Nat) (jo : Nat) (rv : Nat), Eq (OptionType Nat) (sigGet rst jo) (OptionType.some Nat rv) -> Eq (OptionType RecRule) (recrule_in_rules (genRecRulesFrom fam sig u jb rst) (ctorName fam (Nat.add jb jo))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add jb jo)) rv (genRecRhs fam sig u (Nat.add jb jo) rv)))) ",
                // nil case
                "(fun (jb : Nat) (jo : Nat) (rv : Nat) (hh : Eq (OptionType Nat) (sigGet (ListType.nil Nat) jo) (OptionType.some Nat rv)) => option_none_ne_some Nat rv (Eq (OptionType RecRule) (recrule_in_rules (genRecRulesFrom fam sig u jb (ListType.nil Nat)) (ctorName fam (Nat.add jb jo))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add jb jo)) rv (genRecRhs fam sig u (Nat.add jb jo) rv)))) hh) ",
                // cons case
                "(fun (rh : Nat) (rt : ListType Nat) (ih : forall (jb : Nat) (jo : Nat) (rv : Nat), Eq (OptionType Nat) (sigGet rt jo) (OptionType.some Nat rv) -> Eq (OptionType RecRule) (recrule_in_rules (genRecRulesFrom fam sig u jb rt) (ctorName fam (Nat.add jb jo))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add jb jo)) rv (genRecRhs fam sig u (Nat.add jb jo) rv)))) => ",
                "fun (jb : Nat) (jo : Nat) (rv : Nat) (hh : Eq (OptionType Nat) (sigGet (ListType.cons Nat rh rt) jo) (OptionType.some Nat rv)) => ",
                "Nat.rec ",
                // split motive MJ(jj)
                "(fun (jj : Nat) => Eq (OptionType Nat) (sigGet (ListType.cons Nat rh rt) jj) (OptionType.some Nat rv) -> Eq (OptionType RecRule) (recrule_in_rules (genRecRulesFrom fam sig u jb (ListType.cons Nat rh rt)) (ctorName fam (Nat.add jb jj))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add jb jj)) rv (genRecRhs fam sig u (Nat.add jb jj) rv)))) ",
                // ZERO_ARM
                "(fun (hz : Eq (OptionType Nat) (sigGet (ListType.cons Nat rh rt) Nat.zero) (OptionType.some Nat rv)) => ",
                "Eq.substType Bool (fun (bb : Bool) => Eq (OptionType RecRule) (opt_pick RecRule bb (RecRule.mk (ctorName fam jb) rh (genRecRhs fam sig u jb rh)) (recrule_in_rules (genRecRulesFrom fam sig u (Nat.add jb (Nat.succ Nat.zero)) rt) (ctorName fam (Nat.add jb Nat.zero)))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add jb Nat.zero)) rv (genRecRhs fam sig u (Nat.add jb Nat.zero) rv)))) ",
                "Bool.true (name_eqb (ctorName fam jb) (ctorName fam (Nat.add jb Nat.zero))) ",
                "(Eq.symm Bool (name_eqb (ctorName fam jb) (ctorName fam (Nat.add jb Nat.zero))) Bool.true (name_eqb_refl (ctorName fam jb))) ",
                "(Eq.cong Nat (OptionType RecRule) (fun (rr : Nat) => OptionType.some RecRule (RecRule.mk (ctorName fam jb) rr (genRecRhs fam sig u jb rr))) rh rv (option_some_inj Nat rh rv hz))) ",
                // SUCC_ARM
                "(fun (jp : Nat) (ihj : Eq (OptionType Nat) (sigGet (ListType.cons Nat rh rt) jp) (OptionType.some Nat rv) -> Eq (OptionType RecRule) (recrule_in_rules (genRecRulesFrom fam sig u jb (ListType.cons Nat rh rt)) (ctorName fam (Nat.add jb jp))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add jb jp)) rv (genRecRhs fam sig u (Nat.add jb jp) rv)))) => ",
                "fun (hs : Eq (OptionType Nat) (sigGet (ListType.cons Nat rh rt) (Nat.succ jp)) (OptionType.some Nat rv)) => ",
                "Eq.substType Bool (fun (bb : Bool) => Eq (OptionType RecRule) (opt_pick RecRule bb (RecRule.mk (ctorName fam jb) rh (genRecRhs fam sig u jb rh)) (recrule_in_rules (genRecRulesFrom fam sig u (Nat.add jb (Nat.succ Nat.zero)) rt) (ctorName fam (Nat.add jb (Nat.succ jp))))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add jb (Nat.succ jp))) rv (genRecRhs fam sig u (Nat.add jb (Nat.succ jp)) rv)))) ",
                "Bool.false (name_eqb (ctorName fam jb) (ctorName fam (Nat.add jb (Nat.succ jp)))) ",
                "(Eq.symm Bool (name_eqb (ctorName fam jb) (ctorName fam (Nat.add jb (Nat.succ jp)))) Bool.false (Eq.trans Bool (name_eqb (ctorName fam jb) (ctorName fam (Nat.add jb (Nat.succ jp)))) (Bool.and Bool.true (nat_eqb jb (Nat.add jb (Nat.succ jp)))) Bool.false (Eq.cong Bool Bool (fun (bp : Bool) => Bool.and bp (nat_eqb jb (Nat.add jb (Nat.succ jp)))) (name_eqb fam fam) Bool.true (name_eqb_refl fam)) (nat_eqb_self_add_succ_false jb jp))) ",
                "(Eq.substType Nat (fun (ix : Nat) => Eq (OptionType RecRule) (recrule_in_rules (genRecRulesFrom fam sig u (Nat.add jb (Nat.succ Nat.zero)) rt) (ctorName fam ix)) (OptionType.some RecRule (RecRule.mk (ctorName fam ix) rv (genRecRhs fam sig u ix rv)))) (Nat.add (Nat.add jb (Nat.succ Nat.zero)) jp) (Nat.add jb (Nat.succ jp)) (nat_succ_add jb jp) (ih (Nat.add jb (Nat.succ Nat.zero)) jp rv hs))) ",
                // apply the split to jo, then discharge with hh
                "jo hh) ",
                // apply ListType.rec to the major and the generalized args
                "rest j0 j r hjr"
            ),
            "recrule_in_rules (genRecRulesFrom fam sig u j0 rest) (ctorName fam (j0+j)) = the (j0+j) rule when sigGet rest j = some r (ListType.rec on rest; Nat.rec offset split). SnSchema B4b.",
        )?;

        // ── B4b: env-level lookup. recrule_for finds ctor j's rule in genREnv:
        // the recursor's own name matches (name_eqb_refl → opt_pick fires to the
        // rule list), then genRecRulesFrom_lookup at start 0 discharges it
        // (index Nat.add Nat.zero j ↦ j via nat_zero_add). Foundational.
        self.add_recursive_def(
            concat!(
                "def genRecRules_lookup (fam : Name) (sig : ListType Nat) (u : Level) (j : Nat) (r : Nat) ",
                "(hjr : Eq (OptionType Nat) (sigGet sig j) (OptionType.some Nat r)) ",
                ": Eq (OptionType RecRule) (recrule_for (genREnv fam sig u) (genRecName fam sig) (ctorName fam j)) (OptionType.some RecRule (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r))) := ",
                "Eq.substType Bool (fun (bb : Bool) => Eq (OptionType RecRule) (OptionType.rec RecRules (fun (_ : OptionType RecRules) => OptionType RecRule) (OptionType.none RecRule) (fun (rules : RecRules) => recrule_in_rules rules (ctorName fam j)) (opt_pick RecRules bb (genRecRules fam sig u) (OptionType.none RecRules))) (OptionType.some RecRule (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)))) ",
                "Bool.true (name_eqb (genRecName fam sig) (genRecName fam sig)) ",
                "(Eq.symm Bool (name_eqb (genRecName fam sig) (genRecName fam sig)) Bool.true (name_eqb_refl (genRecName fam sig))) ",
                "(Eq.substType Nat (fun (w : Nat) => Eq (OptionType RecRule) (recrule_in_rules (genRecRulesFrom fam sig u Nat.zero sig) (ctorName fam w)) (OptionType.some RecRule (RecRule.mk (ctorName fam w) r (genRecRhs fam sig u w r)))) (Nat.add Nat.zero j) j (nat_zero_add j) (genRecRulesFrom_lookup fam sig u Nat.zero sig j r hjr))"
            ),
            "recrule_for (genREnv fam sig u) (genRecName fam sig) (ctorName fam j) = ctor j's rule when sigGet sig j = some r (name_eqb_refl + genRecRulesFrom_lookup). SnSchema B4b.",
        )?;

        // ── B4b: the generic recursor environment is well-formed. genREnv_ok
        // packages the metadata lookup (genREnv_meta_rec) and the per-ctor rule
        // lookup (genRecRules_lookup) into GenRecEnvOK — the generic analogue of
        // natrec.rs::natREnv_recEnvOK. Consumed by the B5/B6 iota + SN ladder.
        self.add_recursive_def(
            "def genREnv_ok (fam : Name) (sig : ListType Nat) (u : Level) : GenRecEnvOK fam sig u (genREnv fam sig u) := GenRecEnvOK.mk fam sig u (genREnv fam sig u) (genREnv_meta_rec fam sig u) (fun (j : Nat) (r : Nat) (hjr : Eq (OptionType Nat) (sigGet sig j) (OptionType.some Nat r)) => genRecRules_lookup fam sig u j r hjr)",
            "GenRecEnvOK fam sig u (genREnv fam sig u): the generic recursor env carries its metadata + every ctor rule (generic analogue of natREnv_recEnvOK). SnSchema B4b.",
        )?;

        // ── B4b §10a: the Nat→Gen bridges (natContract_to_gen / natFresh_ctor_field
        // / natGenFresh_witness / natFresh_to_genFresh / natRecEnvOK_to_gen) were
        // RELOCATED UP into add_snschema_objects (step B) so the B5 redNatRec_holds
        // re-body can consume them before step C's CandModel. See there.

        // ── B4c foundation: list-append algebra for the schematic iota-fires
        // lemma (iota_fires_gen). list_append recurses on its 1st arg, so the
        // LEFT identity (list_append nil ys = ys, list_append_nil) is rfl, but the
        // RIGHT identity and associativity need structural induction.

        // list_append xs nil = xs (right identity), by ListType.rec on xs.
        self.add_recursive_def(
            "def list_append_nil_right (xs : ListType KExpr) : Eq (ListType KExpr) (list_append xs (ListType.nil KExpr)) xs := ListType.rec KExpr (fun (l : ListType KExpr) => Eq (ListType KExpr) (list_append l (ListType.nil KExpr)) l) (Eq.refl (ListType KExpr) (ListType.nil KExpr)) (fun (x : KExpr) (rest : ListType KExpr) (ih : Eq (ListType KExpr) (list_append rest (ListType.nil KExpr)) rest) => Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => ListType.cons KExpr x L) (list_append rest (ListType.nil KExpr)) rest ih) xs",
            "list_append xs nil = xs (right identity; ListType.rec on xs). SnSchema B4c list algebra.",
        )?;

        // list_append (list_append xs ys) zs = list_append xs (list_append ys zs),
        // by ListType.rec on xs (base uses list_append_nil; step list_append_cons + IH).
        self.add_recursive_def(
            "def list_append_assoc (xs : ListType KExpr) (ys : ListType KExpr) (zs : ListType KExpr) : Eq (ListType KExpr) (list_append (list_append xs ys) zs) (list_append xs (list_append ys zs)) := ListType.rec KExpr (fun (l : ListType KExpr) => Eq (ListType KExpr) (list_append (list_append l ys) zs) (list_append l (list_append ys zs))) (Eq.trans (ListType KExpr) (list_append (list_append (ListType.nil KExpr) ys) zs) (list_append ys zs) (list_append (ListType.nil KExpr) (list_append ys zs)) (Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_append L zs) (list_append (ListType.nil KExpr) ys) ys (list_append_nil ys)) (Eq.symm (ListType KExpr) (list_append (ListType.nil KExpr) (list_append ys zs)) (list_append ys zs) (list_append_nil (list_append ys zs)))) (fun (x : KExpr) (rest : ListType KExpr) (ih : Eq (ListType KExpr) (list_append (list_append rest ys) zs) (list_append rest (list_append ys zs))) => Eq.trans (ListType KExpr) (list_append (list_append (ListType.cons KExpr x rest) ys) zs) (ListType.cons KExpr x (list_append (list_append rest ys) zs)) (list_append (ListType.cons KExpr x rest) (list_append ys zs)) (Eq.trans (ListType KExpr) (list_append (list_append (ListType.cons KExpr x rest) ys) zs) (list_append (ListType.cons KExpr x (list_append rest ys)) zs) (ListType.cons KExpr x (list_append (list_append rest ys) zs)) (Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_append L zs) (list_append (ListType.cons KExpr x rest) ys) (ListType.cons KExpr x (list_append rest ys)) (list_append_cons x rest ys)) (list_append_cons x (list_append rest ys) zs)) (Eq.trans (ListType KExpr) (ListType.cons KExpr x (list_append (list_append rest ys) zs)) (ListType.cons KExpr x (list_append rest (list_append ys zs))) (list_append (ListType.cons KExpr x rest) (list_append ys zs)) (Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => ListType.cons KExpr x L) (list_append (list_append rest ys) zs) (list_append rest (list_append ys zs)) ih) (Eq.symm (ListType KExpr) (list_append (ListType.cons KExpr x rest) (list_append ys zs)) (ListType.cons KExpr x (list_append rest (list_append ys zs))) (list_append_cons x rest (list_append ys zs))))) xs",
            "list_append assoc (ListType.rec on xs; list_append_nil/cons). SnSchema B4c list algebra.",
        )?;

        // kapp_args (apply_spine xs h) = list_append (kapp_args h) xs — apply_spine
        // appends its arg spine to the head's argument list. ListType.rec on xs;
        // cons case pushes h0 into (app h0 x), reassociating via list_append_assoc
        // (kapp_args (app f a) = list_append (kapp_args f) [a] by rfl).
        self.add_recursive_def(
            "def kapp_args_apply_spine (xs : ListType KExpr) (h : KExpr) : Eq (ListType KExpr) (kapp_args (apply_spine xs h)) (list_append (kapp_args h) xs) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (h0 : KExpr), Eq (ListType KExpr) (kapp_args (apply_spine l h0)) (list_append (kapp_args h0) l)) (fun (h0 : KExpr) => Eq.symm (ListType KExpr) (list_append (kapp_args h0) (ListType.nil KExpr)) (kapp_args h0) (list_append_nil_right (kapp_args h0))) (fun (x : KExpr) (rest : ListType KExpr) (ih : forall (h0 : KExpr), Eq (ListType KExpr) (kapp_args (apply_spine rest h0)) (list_append (kapp_args h0) rest)) => fun (h0 : KExpr) => Eq.trans (ListType KExpr) (kapp_args (apply_spine (ListType.cons KExpr x rest) h0)) (list_append (list_append (kapp_args h0) (ListType.cons KExpr x (ListType.nil KExpr))) rest) (list_append (kapp_args h0) (ListType.cons KExpr x rest)) (ih (KExpr.app h0 x)) (list_append_assoc (kapp_args h0) (ListType.cons KExpr x (ListType.nil KExpr)) rest)) xs h",
            "kapp_args (apply_spine xs h) = list_append (kapp_args h) xs (ListType.rec on xs; list_append_assoc). SnSchema B4c list algebra.",
        )?;

        // list_drop (list_length xs + n) (list_append xs ys) = list_drop n ys —
        // dropping the whole prefix xs. ListType.rec on xs; base nat_zero_add,
        // step rewrites list_length (cons ..) + n = succ (..) via nat_succ_add,
        // then list_drop succ + list_tail cons peel the head (rfl) to hit the IH.
        self.add_recursive_def(
            "def list_drop_append_gen (xs : ListType KExpr) (n : Nat) (ys : ListType KExpr) : Eq (ListType KExpr) (list_drop (Nat.add (list_length xs) n) (list_append xs ys)) (list_drop n ys) := ListType.rec KExpr (fun (l : ListType KExpr) => Eq (ListType KExpr) (list_drop (Nat.add (list_length l) n) (list_append l ys)) (list_drop n ys)) (Eq.cong Nat (ListType KExpr) (fun (k : Nat) => list_drop k (list_append (ListType.nil KExpr) ys)) (Nat.add (list_length (ListType.nil KExpr)) n) n (nat_zero_add n)) (fun (x : KExpr) (rest : ListType KExpr) (ih : Eq (ListType KExpr) (list_drop (Nat.add (list_length rest) n) (list_append rest ys)) (list_drop n ys)) => Eq.trans (ListType KExpr) (list_drop (Nat.add (list_length (ListType.cons KExpr x rest)) n) (list_append (ListType.cons KExpr x rest) ys)) (list_drop (Nat.succ (Nat.add (list_length rest) n)) (list_append (ListType.cons KExpr x rest) ys)) (list_drop n ys) (Eq.cong Nat (ListType KExpr) (fun (k : Nat) => list_drop k (list_append (ListType.cons KExpr x rest) ys)) (Nat.add (list_length (ListType.cons KExpr x rest)) n) (Nat.succ (Nat.add (list_length rest) n)) (nat_succ_add (list_length rest) n)) ih) xs",
            "list_drop (list_length xs + n) (list_append xs ys) = list_drop n ys (ListType.rec on xs; nat_succ_add + list_tail peel). SnSchema B4c list algebra.",
        )?;

        // list_take (list_length xs) (list_append xs ys) = xs — taking exactly the
        // prefix xs back. ListType.rec on xs (base rfl; step list_take succ+cons
        // peels the head by rfl, then Eq.cong (cons x) ih). Needed by iota_fires_gen
        // to recover the motive+minors spine [m]++ms from the recursor's argument list.
        self.add_recursive_def(
            "def list_take_append (xs : ListType KExpr) (ys : ListType KExpr) : Eq (ListType KExpr) (list_take (list_length xs) (list_append xs ys)) xs := ListType.rec KExpr (fun (l : ListType KExpr) => Eq (ListType KExpr) (list_take (list_length l) (list_append l ys)) l) (Eq.refl (ListType KExpr) (ListType.nil KExpr)) (fun (x : KExpr) (rest : ListType KExpr) (ih : Eq (ListType KExpr) (list_take (list_length rest) (list_append rest ys)) rest) => Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => ListType.cons KExpr x L) (list_take (list_length rest) (list_append rest ys)) rest ih) xs",
            "list_take (list_length xs) (list_append xs ys) = xs (ListType.rec on xs; take succ+cons rfl peel). SnSchema B4c list algebra.",
        )?;

        // ── B4c: iota_fires_gen sub-evidence haves (factored out of the monolith
        // so each is a localizable, reusable lemma). ifg_hcta: the major's arg
        // list is exactly its fields.
        self.add_recursive_def(
            "def ifg_hcta (fam : Name) (j : Nat) (fields : ListType KExpr) : Eq (ListType KExpr) (kapp_args (ctorApp fam j fields)) fields := Eq.trans (ListType KExpr) (kapp_args (ctorApp fam j fields)) (list_append (kapp_args (ctorC fam j)) fields) fields (kapp_args_apply_spine fields (ctorC fam j)) (list_append_nil fields)",
            "kapp_args (ctorApp fam j fields) = fields (kapp_args_apply_spine + list_append_nil). SnSchema B4c iota_fires_gen have.",
        )?;

        // ifg_hsum: the recursor's major-slot prefix count (num_params+motives+
        // minors+indices of genRecMeta sig = 0+1+sigLength sig+0) equals
        // list_length (cons m ms) = succ (list_length ms).
        self.add_recursive_def(
            "def ifg_hsum (sig : ListType Nat) (m : KExpr) (ms : ListType KExpr) (hms : Eq Nat (list_length ms) (sigLength sig)) : Eq Nat (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig))) (list_length (ListType.cons KExpr m ms)) := Eq.trans Nat (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig))) (Nat.succ (Nat.add Nat.zero (sigLength sig))) (list_length (ListType.cons KExpr m ms)) (nat_succ_add Nat.zero (sigLength sig)) (Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (Nat.add Nat.zero (sigLength sig)) (list_length ms) (Eq.trans Nat (Nat.add Nat.zero (sigLength sig)) (sigLength sig) (list_length ms) (nat_zero_add (sigLength sig)) (Eq.symm Nat (list_length ms) (sigLength sig) hms)))",
            "prefix count (genRecMeta sig) = list_length (cons m ms) (nat_succ_add + nat_zero_add + hms). SnSchema B4c iota_fires_gen have.",
        )?;

        // ifg_hsub: sub (list_length (kapp_args MAJ)) (recrule_num_fields RULE) = 0,
        // i.e. list_length fields - r = r - r = 0.
        self.add_recursive_def(
            "def ifg_hsub (fam : Name) (sig : ListType Nat) (u : Level) (j : Nat) (r : Nat) (fields : ListType KExpr) (hfl : Eq Nat (list_length fields) r) : Eq Nat (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) (recrule_num_fields (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)))) Nat.zero := Eq.trans Nat (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) r) (Nat.sub r r) Nat.zero (Eq.cong Nat Nat (fun (w : Nat) => Nat.sub w r) (list_length (kapp_args (ctorApp fam j fields))) r (Eq.trans Nat (list_length (kapp_args (ctorApp fam j fields))) (list_length fields) r (Eq.cong (ListType KExpr) Nat (fun (L : ListType KExpr) => list_length L) (kapp_args (ctorApp fam j fields)) fields (ifg_hcta fam j fields)) hfl)) (nat_sub_self r)",
            "sub (list_length (kapp_args MAJ)) (recrule_num_fields RULE) = 0 (ifg_hcta + hfl + nat_sub_self). SnSchema B4c iota_fires_gen have.",
        )?;

        // ifg_hfn: the recursor application's head const name = genRecName fam sig.
        self.add_recursive_def(
            "def ifg_hfn (fam : Name) (sig : ListType Nat) (u : Level) (m : KExpr) (ms : ListType KExpr) (j : Nat) (fields : ListType KExpr) : Eq (OptionType Name) (kexpr_const_name (kapp_fn (genRecApp fam sig u m ms (ctorApp fam j fields)))) (OptionType.some Name (genRecName fam sig)) := Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn (genRecApp fam sig u m ms (ctorApp fam j fields)))) (kexpr_const_name (kapp_fn (genRecC fam sig u))) (OptionType.some Name (genRecName fam sig)) (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn (genRecApp fam sig u m ms (ctorApp fam j fields))) (kapp_fn (genRecC fam sig u)) (kapp_fn_apply_spine (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))) (genRecC fam sig u))) (Eq.refl (OptionType Name) (OptionType.some Name (genRecName fam sig)))",
            "kexpr_const_name (kapp_fn (genRecApp ..)) = some (genRecName fam sig) (kapp_fn_apply_spine). SnSchema B4c iota_fires_gen have.",
        )?;

        // ifg_hct: the major's head const name = ctorName fam j.
        self.add_recursive_def(
            "def ifg_hct (fam : Name) (j : Nat) (fields : ListType KExpr) : Eq (OptionType Name) (kexpr_const_name (kapp_fn (ctorApp fam j fields))) (OptionType.some Name (ctorName fam j)) := Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn (ctorApp fam j fields))) (kexpr_const_name (kapp_fn (ctorC fam j))) (OptionType.some Name (ctorName fam j)) (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn (ctorApp fam j fields)) (kapp_fn (ctorC fam j)) (kapp_fn_apply_spine fields (ctorC fam j))) (Eq.refl (OptionType Name) (OptionType.some Name (ctorName fam j)))",
            "kexpr_const_name (kapp_fn (ctorApp fam j fields)) = some (ctorName fam j) (kapp_fn_apply_spine). SnSchema B4c iota_fires_gen have.",
        )?;

        // ifg_hargs: the recursor application's argument list = [m] ++ ms ++ [major].
        self.add_recursive_def(
            "def ifg_hargs (fam : Name) (sig : ListType Nat) (u : Level) (m : KExpr) (ms : ListType KExpr) (j : Nat) (fields : ListType KExpr) : Eq (ListType KExpr) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields))) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))) := Eq.trans (ListType KExpr) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields))) (list_append (kapp_args (genRecC fam sig u)) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr))))) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))) (kapp_args_apply_spine (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))) (genRecC fam sig u)) (list_append_nil (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))))",
            "kapp_args (genRecApp ..) = [m]++ms++[major] (kapp_args_apply_spine + list_append_nil). SnSchema B4c iota_fires_gen have.",
        )?;

        // ifg_h3a2: rewrite the drop count (recmeta prefix of genRecMeta sig) to
        // list_length (cons m ms) via ifg_hsum. WORKAROUND: the elaborator rejects
        // `fun (q : Nat) => list_head (list_drop q XS)` (a bound Nat var as
        // list_drop's Nat.rec major fails to elaborate; a fixed neutral count is
        // fine). So we cong on the BARE `list_drop` (partial app, no lambda-bound
        // major), then apply the resulting function-equality to XS via `fun g => g
        // XS`, then wrap with list_head.
        self.add_recursive_def(
            "def ifg_h3a2 (fam : Name) (sig : ListType Nat) (u : Level) (m : KExpr) (ms : ListType KExpr) (j : Nat) (fields : ListType KExpr) (hms : Eq Nat (list_length ms) (sigLength sig)) : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig))) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))))) (list_head (list_drop (list_length (ListType.cons KExpr m ms)) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))))) := Eq.cong (ListType KExpr) (OptionType KExpr) list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig))) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr))))) (list_drop (list_length (ListType.cons KExpr m ms)) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr))))) (Eq.cong (ListType KExpr -> ListType KExpr) (ListType KExpr) (fun (g : ListType KExpr -> ListType KExpr) => g (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr))))) (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (list_drop (list_length (ListType.cons KExpr m ms))) (Eq.cong Nat (ListType KExpr -> ListType KExpr) list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig))) (list_length (ListType.cons KExpr m ms)) (ifg_hsum sig m ms hms)))",
            "ifg_h3 count-rewrite (bare list_drop cong; avoids bound-var Nat.rec major). SnSchema B4c.",
        )?;
        // ifg_h3a: first half — rewrite args->XS (ifg_hargs) then drop-count->
        // list_length (cons m ms) (ifg_h3a2), both under list_head(list_drop _ _).
        self.add_recursive_def(
            "def ifg_h3a (fam : Name) (sig : ListType Nat) (u : Level) (m : KExpr) (ms : ListType KExpr) (j : Nat) (fields : ListType KExpr) (hms : Eq Nat (list_length ms) (sigLength sig)) : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields))))) (list_head (list_drop (list_length (ListType.cons KExpr m ms)) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))))) := Eq.trans (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields))))) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig))) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))))) (list_head (list_drop (list_length (ListType.cons KExpr m ms)) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))))) (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig))) L)) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields))) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))) (ifg_hargs fam sig u m ms j fields)) (ifg_h3a2 fam sig u m ms j fields hms)",
            "ifg_h3 first half (args->XS via ifg_hargs, count->len via ifg_h3a2). SnSchema B4c.",
        )?;
        // ifg_h3b: second half — list_drop_append_gen peels the [m]++ms prefix to
        // leave [major], then list_head_cons reads it off.
        self.add_recursive_def(
            "def ifg_h3b (fam : Name) (m : KExpr) (ms : ListType KExpr) (j : Nat) (fields : ListType KExpr) : Eq (OptionType KExpr) (list_head (list_drop (list_length (ListType.cons KExpr m ms)) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))))) (OptionType.some KExpr (ctorApp fam j fields)) := Eq.trans (OptionType KExpr) (list_head (list_drop (list_length (ListType.cons KExpr m ms)) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))))) (list_head (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr))) (OptionType.some KExpr (ctorApp fam j fields)) (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head L) (list_drop (list_length (ListType.cons KExpr m ms)) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr))))) (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)) (list_drop_append_gen (ListType.cons KExpr m ms) Nat.zero (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))) (list_head_cons (ctorApp fam j fields) (ListType.nil KExpr))",
            "ifg_h3 second half (list_drop_append_gen peel + list_head_cons). SnSchema B4c.",
        )?;
        self.add_recursive_def(
            "def ifg_h3 (fam : Name) (sig : ListType Nat) (u : Level) (m : KExpr) (ms : ListType KExpr) (j : Nat) (fields : ListType KExpr) (hms : Eq Nat (list_length ms) (sigLength sig)) : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields))))) (OptionType.some KExpr (ctorApp fam j fields)) := Eq.trans (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields))))) (list_head (list_drop (list_length (ListType.cons KExpr m ms)) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))))) (OptionType.some KExpr (ctorApp fam j fields)) (ifg_h3a fam sig u m ms j fields hms) (ifg_h3b fam m ms j fields)",
            "list_head (list_drop prefix (kapp_args (genRecApp ..))) = some (ctorApp fam j fields) (ifg_h3a + ifg_h3b). SnSchema B4c iota_fires_gen have.",
        )?;

        // ── B4c: the final-reassembly count-rewrites (hT/hF/hD), each via the
        // bare-list_take/list_drop cong workaround (no bound var in the Nat.rec
        // major). ifg_hT: list_take P3 (kapp_args E) = [m]++ms.
        self.add_recursive_def(
            "def ifg_hT (fam : Name) (sig : ListType Nat) (u : Level) (m : KExpr) (ms : ListType KExpr) (j : Nat) (fields : ListType KExpr) (hms : Eq Nat (list_length ms) (sigLength sig)) : Eq (ListType KExpr) (list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (ListType.cons KExpr m ms) := Eq.trans (ListType KExpr) (list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (list_take (list_length (ListType.cons KExpr m ms)) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr))))) (ListType.cons KExpr m ms) (Eq.trans (ListType KExpr) (list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr))))) (list_take (list_length (ListType.cons KExpr m ms)) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr))))) (Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) L) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields))) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))) (ifg_hargs fam sig u m ms j fields)) (Eq.cong (ListType KExpr -> ListType KExpr) (ListType KExpr) (fun (g : ListType KExpr -> ListType KExpr) => g (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr))))) (list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig)))) (list_take (list_length (ListType.cons KExpr m ms))) (Eq.cong Nat (ListType KExpr -> ListType KExpr) list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (list_length (ListType.cons KExpr m ms)) (ifg_hsum sig m ms hms)))) (list_take_append (ListType.cons KExpr m ms) (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))",
            "list_take P3 (kapp_args E) = [m]++ms (ifg_hargs + ifg_hsum bare-cong + list_take_append). SnSchema B4c iota_fires_gen have.",
        )?;

        // ifg_hF: list_drop (list_length (kapp_args MAJ) - r) (kapp_args MAJ) = fields.
        self.add_recursive_def(
            "def ifg_hF (fam : Name) (sig : ListType Nat) (u : Level) (j : Nat) (r : Nat) (fields : ListType KExpr) (hfl : Eq Nat (list_length fields) r) : Eq (ListType KExpr) (list_drop (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) (recrule_num_fields (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)))) (kapp_args (ctorApp fam j fields))) fields := Eq.trans (ListType KExpr) (list_drop (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) (recrule_num_fields (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)))) (kapp_args (ctorApp fam j fields))) (list_drop Nat.zero (kapp_args (ctorApp fam j fields))) fields (Eq.cong (ListType KExpr -> ListType KExpr) (ListType KExpr) (fun (g : ListType KExpr -> ListType KExpr) => g (kapp_args (ctorApp fam j fields))) (list_drop (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) (recrule_num_fields (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r))))) (list_drop Nat.zero) (Eq.cong Nat (ListType KExpr -> ListType KExpr) list_drop (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) (recrule_num_fields (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)))) Nat.zero (ifg_hsub fam sig u j r fields hfl))) (ifg_hcta fam j fields)",
            "list_drop (list_length (kapp_args MAJ) - r) (kapp_args MAJ) = fields (ifg_hsub bare-cong + list_drop_zero + ifg_hcta). SnSchema B4c iota_fires_gen have.",
        )?;

        // ifg_hD: list_drop (succ P4) (kapp_args E) = nil.
        self.add_recursive_def(
            "def ifg_hD (fam : Name) (sig : ListType Nat) (u : Level) (m : KExpr) (ms : ListType KExpr) (j : Nat) (fields : ListType KExpr) (hms : Eq Nat (list_length ms) (sigLength sig)) : Eq (ListType KExpr) (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (ListType.nil KExpr) := Eq.trans (ListType KExpr) (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (list_drop (Nat.succ (list_length (ListType.cons KExpr m ms))) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr))))) (ListType.nil KExpr) (Eq.trans (ListType KExpr) (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr))))) (list_drop (Nat.succ (list_length (ListType.cons KExpr m ms))) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr))))) (Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) L) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields))) (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))) (ifg_hargs fam sig u m ms j fields)) (Eq.cong (ListType KExpr -> ListType KExpr) (ListType KExpr) (fun (g : ListType KExpr -> ListType KExpr) => g (ListType.cons KExpr m (list_append ms (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr))))) (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig))))) (list_drop (Nat.succ (list_length (ListType.cons KExpr m ms)))) (Eq.cong Nat (ListType KExpr -> ListType KExpr) list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (Nat.succ (list_length (ListType.cons KExpr m ms))) (Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig))) (list_length (ListType.cons KExpr m ms)) (ifg_hsum sig m ms hms))))) (list_drop_append_gen (ListType.cons KExpr m ms) (Nat.succ Nat.zero) (ListType.cons KExpr (ctorApp fam j fields) (ListType.nil KExpr)))",
            "list_drop (succ P4) (kapp_args E) = nil (ifg_hargs + succ-count bare-cong + list_drop_append_gen). SnSchema B4c iota_fires_gen have.",
        )?;

        // ifg_hfinal: the iota_reduct OUTPUT (apply_spine D (apply_spine F
        // (apply_spine T rhs))) equals the pre-beta contractum apply_spine fields
        // (apply_spine [m]++ms (genRecRhs..)). Rewrites the innermost spine T->[m]++ms
        // (ifg_hT), F->fields (ifg_hF), D->nil (ifg_hD), each under apply_spine congs.
        self.add_recursive_def(
            "def ifg_hfinal (fam : Name) (sig : ListType Nat) (u : Level) (m : KExpr) (ms : ListType KExpr) (j : Nat) (r : Nat) (fields : ListType KExpr) (hms : Eq Nat (list_length ms) (sigLength sig)) (hfl : Eq Nat (list_length fields) r) : Eq KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) (recrule_num_fields (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)))) (kapp_args (ctorApp fam j fields))) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (genRecRhs fam sig u j r)))) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) := Eq.trans KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) (recrule_num_fields (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)))) (kapp_args (ctorApp fam j fields))) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (genRecRhs fam sig u j r)))) (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r)))) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) (Eq.trans KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) (recrule_num_fields (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)))) (kapp_args (ctorApp fam j fields))) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (genRecRhs fam sig u j r)))) (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) (recrule_num_fields (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)))) (kapp_args (ctorApp fam j fields))) (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r)))) (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r)))) (Eq.cong KExpr KExpr (fun (Z : KExpr) => apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) (recrule_num_fields (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)))) (kapp_args (ctorApp fam j fields))) Z)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (genRecRhs fam sig u j r)) (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r)) (Eq.cong (ListType KExpr) KExpr (fun (L : ListType KExpr) => apply_spine L (genRecRhs fam sig u j r)) (list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (ListType.cons KExpr m ms) (ifg_hT fam sig u m ms j fields hms))) (Eq.cong KExpr KExpr (fun (Z : KExpr) => apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) Z) (apply_spine (list_drop (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) (recrule_num_fields (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)))) (kapp_args (ctorApp fam j fields))) (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) (Eq.cong (ListType KExpr) KExpr (fun (L : ListType KExpr) => apply_spine L (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) (list_drop (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) (recrule_num_fields (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)))) (kapp_args (ctorApp fam j fields))) fields (ifg_hF fam sig u j r fields hfl)))) (Eq.cong (ListType KExpr) KExpr (fun (L : ListType KExpr) => apply_spine L (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r)))) (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (ListType.nil KExpr) (ifg_hD fam sig u m ms j fields hms))",
            "iota_reduct output = pre-beta contractum apply_spine fields (apply_spine [m]++ms genRecRhs) (ifg_hT/hF/hD reassembly). SnSchema B4c iota_fires_gen have.",
        )?;

        // ── B4c: THE SCHEMATIC IOTA HEAD FIRE. iota_reduct genuinely computes the
        // generic recursor's contractum: opt_bind_some_intro x5 walks the iota_reduct
        // opt_bind chain (kexpr_const_name -> recmeta_for -> major slot -> ctor name
        // -> recrule_for), discharging each layer with a proven have (ifg_hfn /
        // genREnv_meta_rec / ifg_h3 / ifg_hct / genRecRules_lookup), then wraps
        // ifg_hfinal for the pre-beta reassembly. Mirrors iota_reduct_app_over
        // (iota_core.rs:1555). NOT rfl (abstract fam/sig); the load-bearing brick.
        self.add_recursive_def(
            "def iota_fires_gen (fam : Name) (sig : ListType Nat) (u : Level) (m : KExpr) (ms : ListType KExpr) (j : Nat) (r : Nat) (fields : ListType KExpr) (hms : Eq Nat (list_length ms) (sigLength sig)) (hjr : Eq (OptionType Nat) (sigGet sig j) (OptionType.some Nat r)) (hfl : Eq Nat (list_length fields) r) : Eq (OptionType KExpr) (iota_reduct (genREnv fam sig u) (genRecApp fam sig u m ms (ctorApp fam j fields))) (OptionType.some KExpr (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r)))) := opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn (genRecApp fam sig u m ms (ctorApp fam j fields)))) (fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for (genREnv fam sig u) recname) (fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields))))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (genREnv fam sig u) recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (recrule_rhs rule))))))))) (genRecName fam sig) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) (ifg_hfn fam sig u m ms j fields) (opt_bind_some_intro RecMeta KExpr (recmeta_for (genREnv fam sig u) (genRecName fam sig)) (fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields))))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (genREnv fam sig u) (genRecName fam sig) cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (recrule_rhs rule)))))))) (genRecMeta sig) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) (genREnv_meta_rec fam sig u) (opt_bind_some_intro KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields))))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (genREnv fam sig u) (genRecName fam sig) cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (recrule_rhs rule))))))) (ctorApp fam j fields) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) (ifg_h3 fam sig u m ms j fields hms) (opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn (ctorApp fam j fields))) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for (genREnv fam sig u) (genRecName fam sig) cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) (recrule_num_fields rule)) (kapp_args (ctorApp fam j fields))) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (recrule_rhs rule)))))) (ctorName fam j) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) (ifg_hct fam j fields) (opt_bind_some_intro RecRule KExpr (recrule_for (genREnv fam sig u) (genRecName fam sig) (ctorName fam j)) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) (recrule_num_fields rule)) (kapp_args (ctorApp fam j fields))) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (recrule_rhs rule))))) (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) (genRecRules_lookup fam sig u j r hjr) (Eq.cong KExpr (OptionType KExpr) (fun (X : KExpr) => OptionType.some KExpr X) (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (recmeta_num_indices (genRecMeta sig)))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args (ctorApp fam j fields))) (recrule_num_fields (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)))) (kapp_args (ctorApp fam j fields))) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params (genRecMeta sig)) (recmeta_num_motives (genRecMeta sig))) (recmeta_num_minors (genRecMeta sig))) (kapp_args (genRecApp fam sig u m ms (ctorApp fam j fields)))) (recrule_rhs (RecRule.mk (ctorName fam j) r (genRecRhs fam sig u j r)))))) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) (ifg_hfinal fam sig u m ms j r fields hms hfl))))))",
            "THE schematic iota HEAD fire: iota_reduct (genREnv fam sig u) (genRecApp .. (ctorApp fam j fields)) = some (apply_spine fields (apply_spine [m]++ms (genRecRhs fam sig u j r))) given the gates (opt_bind_some_intro x5 over the proven haves). SnSchema B4c.",
        )?;

        // ── B4c: β-telescope support lemmas (toward lamTel_beta).
        // betaReduces_spine_head: a head β-step lifts through an argument spine.
        self.add_recursive_def(
            "def betaReduces_spine_head (args : ListType KExpr) : forall (e : KExpr) (e2 : KExpr), beta_reduces e e2 -> beta_reduces (apply_spine args e) (apply_spine args e2) := ListType.rec KExpr (fun (a0 : ListType KExpr) => forall (e : KExpr) (e2 : KExpr), beta_reduces e e2 -> beta_reduces (apply_spine a0 e) (apply_spine a0 e2)) (fun (e : KExpr) (e2 : KExpr) (h : beta_reduces e e2) => h) (fun (x : KExpr) (rest : ListType KExpr) (ih : forall (e : KExpr) (e2 : KExpr), beta_reduces e e2 -> beta_reduces (apply_spine rest e) (apply_spine rest e2)) => fun (e : KExpr) (e2 : KExpr) (h : beta_reduces e e2) => ih (KExpr.app e x) (KExpr.app e2 x) (beta_reduces.app_left e e2 x h)) args",
            "beta_reduces e e2 -> beta_reduces (apply_spine args e) (apply_spine args e2) (ListType.rec on args; beta_reduces.app_left). SnSchema B4c.",
        )?;
        // instDomsAt_length: instDomsAt preserves length.
        self.add_recursive_def(
            "def instDomsAt_length (doms : ListType KExpr) (a : KExpr) : forall (dep : Nat), Eq Nat (list_length (instDomsAt doms a dep)) (list_length doms) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (dep : Nat), Eq Nat (list_length (instDomsAt l a dep)) (list_length l)) (fun (dep : Nat) => Eq.refl Nat Nat.zero) (fun (d : KExpr) (rest : ListType KExpr) (ih : forall (dep : Nat), Eq Nat (list_length (instDomsAt rest a dep)) (list_length rest)) => fun (dep : Nat) => Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (list_length (instDomsAt rest a (Nat.add dep (Nat.succ Nat.zero)))) (list_length rest) (ih (Nat.add dep (Nat.succ Nat.zero)))) doms",
            "list_length (instDomsAt doms a dep) = list_length doms (ListType.rec on doms; motive over dep). SnSchema B4c.",
        )?;
        // minorTys_length = sigLength sig.
        self.add_recursive_def(
            "def minorTys_length (fam : Name) (j : Nat) (sig : ListType Nat) : Eq Nat (list_length (minorTys fam j sig)) (sigLength sig) := ListType.rec Nat (fun (s : ListType Nat) => forall (j0 : Nat), Eq Nat (list_length (minorTys fam j0 s)) (sigLength s)) (fun (j0 : Nat) => Eq.refl Nat Nat.zero) (fun (r : Nat) (rest : ListType Nat) (ih : forall (j0 : Nat), Eq Nat (list_length (minorTys fam j0 rest)) (sigLength rest)) => fun (j0 : Nat) => Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (list_length (minorTys fam (Nat.add j0 (Nat.succ Nat.zero)) rest)) (sigLength rest) (ih (Nat.add j0 (Nat.succ Nat.zero)))) sig j",
            "list_length (minorTys fam j sig) = sigLength sig (ListType.rec on sig; motive over j). SnSchema B4c.",
        )?;
        // replicateLT_length = n.
        self.add_recursive_def(
            "def replicateLT_length (n : Nat) (x : KExpr) : Eq Nat (list_length (replicateLT n x)) n := Nat.rec (fun (n0 : Nat) => Eq Nat (list_length (replicateLT n0 x)) n0) (Eq.refl Nat Nat.zero) (fun (n0 : Nat) (ih : Eq Nat (list_length (replicateLT n0 x)) n0) => Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (list_length (replicateLT n0 x)) n0 ih) n",
            "list_length (replicateLT n x) = n (Nat.rec on n). SnSchema B4c.",
        )?;
        // genSteps_of_betaStar: lift a pure β* into the generic step relation.
        self.add_recursive_def(
            "def genSteps_of_betaStar (fam : Name) (sig : ListType Nat) (u : Level) (a : KExpr) (b : KExpr) (h : beta_reduces_star a b) : genSteps fam sig u a b := beta_reduces_star.rec (fun (x : KExpr) (y : KExpr) (_ : beta_reduces_star x y) => genSteps fam sig u x y) (fun (e : KExpr) => genSteps.refl fam sig u e) (fun (e : KExpr) (e2 : KExpr) (e3 : KExpr) (st : beta_reduces e e2) (_rest : beta_reduces_star e2 e3) (ih : genSteps fam sig u e2 e3) => genSteps.step fam sig u e e2 e3 (genStep.beta fam sig u e e2 st) ih) a b h",
            "beta_reduces_star a b -> genSteps fam sig u a b (beta_reduces_star.rec; genStep.beta). SnSchema B4c.",
        )?;

        // inst_lamTel: pushing an instantiate_at through a lamTel — the depth-shift
        // identity that lets lamTel_beta's head redex re-fold into a smaller lamTel.
        // Induction on doms; step = Eq.cong under lam over the IH at depth succ dep,
        // then a nat_succ_add transport of the body's instantiate depth.
        self.add_recursive_def(
            "def inst_lamTel (a : KExpr) (doms : ListType KExpr) : forall (dep : Nat) (body : KExpr), Eq KExpr (instantiate_at (lamTel doms body) a dep) (lamTel (instDomsAt doms a dep) (instantiate_at body a (Nat.add dep (list_length doms)))) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (dep : Nat) (body : KExpr), Eq KExpr (instantiate_at (lamTel l body) a dep) (lamTel (instDomsAt l a dep) (instantiate_at body a (Nat.add dep (list_length l))))) (fun (dep : Nat) (body : KExpr) => Eq.refl KExpr (instantiate_at body a dep)) (fun (d : KExpr) (rest : ListType KExpr) (ih : forall (dep : Nat) (body : KExpr), Eq KExpr (instantiate_at (lamTel rest body) a dep) (lamTel (instDomsAt rest a dep) (instantiate_at body a (Nat.add dep (list_length rest))))) => fun (dep : Nat) (body : KExpr) => Eq.trans KExpr (instantiate_at (lamTel (ListType.cons KExpr d rest) body) a dep) (KExpr.lam (instantiate_at d a dep) (lamTel (instDomsAt rest a (Nat.succ dep)) (instantiate_at body a (Nat.add (Nat.succ dep) (list_length rest))))) (lamTel (instDomsAt (ListType.cons KExpr d rest) a dep) (instantiate_at body a (Nat.add dep (list_length (ListType.cons KExpr d rest))))) (Eq.cong KExpr KExpr (fun (Y : KExpr) => KExpr.lam (instantiate_at d a dep) Y) (instantiate_at (lamTel rest body) a (Nat.succ dep)) (lamTel (instDomsAt rest a (Nat.succ dep)) (instantiate_at body a (Nat.add (Nat.succ dep) (list_length rest)))) (ih (Nat.succ dep) body)) (Eq.cong Nat KExpr (fun (Z : Nat) => KExpr.lam (instantiate_at d a dep) (lamTel (instDomsAt rest a (Nat.succ dep)) (instantiate_at body a Z))) (Nat.add (Nat.succ dep) (list_length rest)) (Nat.add dep (Nat.succ (list_length rest))) (nat_succ_add dep (list_length rest)))) doms",
            "instantiate_at (lamTel doms body) a dep = lamTel (instDomsAt doms a dep) (instantiate_at body a (dep + len doms)) (ListType.rec on doms; nat_succ_add depth transport). SnSchema B4c.",
        )?;

        // ── B4c: lamTel_beta — THE β-telescope engine. Applying a lamTel to a
        // matching-length argument spine β-reduces (over genSteps) to the iterated
        // instantiation. Induction on args; nested doms case (mismatched lengths
        // absurd via nat_zero_ne_succ); each step: one head β (betaReduces_spine_head
        // o beta_reduces.beta) then the IH at (instDomsAt doms' a 0, args'),
        // transported through inst_lamTel (start) + an instIter-depth cong (end).
        self.add_recursive_def(
            "def lamTel_beta (fam : Name) (sig : ListType Nat) (u : Level) (args : ListType KExpr) : forall (doms : ListType KExpr) (body : KExpr), Eq Nat (list_length args) (list_length doms) -> genSteps fam sig u (apply_spine args (lamTel doms body)) (instIter body args) := ListType.rec KExpr (fun (al : ListType KExpr) => forall (doms : ListType KExpr) (body : KExpr), Eq Nat (list_length al) (list_length doms) -> genSteps fam sig u (apply_spine al (lamTel doms body)) (instIter body al)) (fun (doms : ListType KExpr) (body : KExpr) (hlen : Eq Nat (list_length (ListType.nil KExpr)) (list_length doms)) => ListType.rec KExpr (fun (dl : ListType KExpr) => Eq Nat (list_length (ListType.nil KExpr)) (list_length dl) -> genSteps fam sig u (apply_spine (ListType.nil KExpr) (lamTel dl body)) (instIter body (ListType.nil KExpr))) (fun (h : Eq Nat (list_length (ListType.nil KExpr)) (list_length (ListType.nil KExpr))) => genSteps.refl fam sig u body) (fun (d : KExpr) (rest : ListType KExpr) (_ihd : Eq Nat (list_length (ListType.nil KExpr)) (list_length rest) -> genSteps fam sig u (apply_spine (ListType.nil KExpr) (lamTel rest body)) (instIter body (ListType.nil KExpr))) (h : Eq Nat (list_length (ListType.nil KExpr)) (list_length (ListType.cons KExpr d rest))) => nat_zero_ne_succ (list_length rest) (genSteps fam sig u (apply_spine (ListType.nil KExpr) (lamTel (ListType.cons KExpr d rest) body)) (instIter body (ListType.nil KExpr))) h) doms hlen) (fun (a : KExpr) (args2 : ListType KExpr) (ih_args : forall (doms : ListType KExpr) (body : KExpr), Eq Nat (list_length args2) (list_length doms) -> genSteps fam sig u (apply_spine args2 (lamTel doms body)) (instIter body args2)) => fun (doms : ListType KExpr) (body : KExpr) (hlen : Eq Nat (list_length (ListType.cons KExpr a args2)) (list_length doms)) => ListType.rec KExpr (fun (dl : ListType KExpr) => Eq Nat (list_length (ListType.cons KExpr a args2)) (list_length dl) -> genSteps fam sig u (apply_spine (ListType.cons KExpr a args2) (lamTel dl body)) (instIter body (ListType.cons KExpr a args2))) (fun (h : Eq Nat (list_length (ListType.cons KExpr a args2)) (list_length (ListType.nil KExpr))) => nat_zero_ne_succ (list_length args2) (genSteps fam sig u (apply_spine (ListType.cons KExpr a args2) (lamTel (ListType.nil KExpr) body)) (instIter body (ListType.cons KExpr a args2))) (Eq.symm Nat (list_length (ListType.cons KExpr a args2)) (list_length (ListType.nil KExpr)) h)) (fun (d : KExpr) (doms2 : ListType KExpr) (_ihd : Eq Nat (list_length (ListType.cons KExpr a args2)) (list_length doms2) -> genSteps fam sig u (apply_spine (ListType.cons KExpr a args2) (lamTel doms2 body)) (instIter body (ListType.cons KExpr a args2))) (h : Eq Nat (list_length (ListType.cons KExpr a args2)) (list_length (ListType.cons KExpr d doms2))) => genSteps.step fam sig u (apply_spine (ListType.cons KExpr a args2) (lamTel (ListType.cons KExpr d doms2) body)) (apply_spine args2 (instantiate (lamTel doms2 body) a)) (instIter body (ListType.cons KExpr a args2)) (genStep.beta fam sig u (apply_spine args2 (KExpr.app (KExpr.lam d (lamTel doms2 body)) a)) (apply_spine args2 (instantiate (lamTel doms2 body) a)) (betaReduces_spine_head args2 (KExpr.app (KExpr.lam d (lamTel doms2 body)) a) (instantiate (lamTel doms2 body) a) (beta_reduces.beta d (lamTel doms2 body) a))) (Eq.substType KExpr (fun (S : KExpr) => genSteps fam sig u S (instIter body (ListType.cons KExpr a args2))) (apply_spine args2 (lamTel (instDomsAt doms2 a Nat.zero) (instantiate_at body a (Nat.add Nat.zero (list_length doms2))))) (apply_spine args2 (instantiate (lamTel doms2 body) a)) (Eq.cong KExpr KExpr (fun (X : KExpr) => apply_spine args2 X) (lamTel (instDomsAt doms2 a Nat.zero) (instantiate_at body a (Nat.add Nat.zero (list_length doms2)))) (instantiate (lamTel doms2 body) a) (Eq.symm KExpr (instantiate (lamTel doms2 body) a) (lamTel (instDomsAt doms2 a Nat.zero) (instantiate_at body a (Nat.add Nat.zero (list_length doms2)))) (inst_lamTel a doms2 Nat.zero body))) (Eq.substType KExpr (fun (E : KExpr) => genSteps fam sig u (apply_spine args2 (lamTel (instDomsAt doms2 a Nat.zero) (instantiate_at body a (Nat.add Nat.zero (list_length doms2))))) E) (instIter (instantiate_at body a (Nat.add Nat.zero (list_length doms2))) args2) (instIter body (ListType.cons KExpr a args2)) (Eq.cong Nat KExpr (fun (Z : Nat) => instIter (instantiate_at body a Z) args2) (Nat.add Nat.zero (list_length doms2)) (list_length args2) (Eq.trans Nat (Nat.add Nat.zero (list_length doms2)) (list_length doms2) (list_length args2) (nat_zero_add (list_length doms2)) (Eq.symm Nat (list_length args2) (list_length doms2) (nat_succ_inj (list_length args2) (list_length doms2) h)))) (ih_args (instDomsAt doms2 a Nat.zero) (instantiate_at body a (Nat.add Nat.zero (list_length doms2))) (Eq.trans Nat (list_length args2) (list_length doms2) (list_length (instDomsAt doms2 a Nat.zero)) (nat_succ_inj (list_length args2) (list_length doms2) h) (Eq.symm Nat (list_length (instDomsAt doms2 a Nat.zero)) (list_length doms2) (instDomsAt_length doms2 a Nat.zero))))))) doms hlen) args",
            "lamTel_beta: apply_spine args (lamTel doms body) ->* instIter body args over genSteps when lengths match (double induction; head beta lifted via betaReduces_spine_head; IH transported via inst_lamTel + instDomsAt_length). SnSchema B4c THE beta-telescope engine.",
        )?;

        // ── B4c: genRecRhs_eq_lamTel — rewrite genRecRhs as a lamTel over its
        // domain telescope, so lamTel_beta applies. Via three structural rewrites.
        self.add_recursive_def(
            "def lamTel_append (xs : ListType KExpr) (ys : ListType KExpr) (body : KExpr) : Eq KExpr (lamTel (list_append xs ys) body) (lamTel xs (lamTel ys body)) := ListType.rec KExpr (fun (l : ListType KExpr) => Eq KExpr (lamTel (list_append l ys) body) (lamTel l (lamTel ys body))) (Eq.refl KExpr (lamTel ys body)) (fun (d : KExpr) (rest : ListType KExpr) (ih : Eq KExpr (lamTel (list_append rest ys) body) (lamTel rest (lamTel ys body))) => Eq.cong KExpr KExpr (fun (Y : KExpr) => KExpr.lam d Y) (lamTel (list_append rest ys) body) (lamTel rest (lamTel ys body)) ih) xs",
            "lamTel (list_append xs ys) body = lamTel xs (lamTel ys body) (ListType.rec on xs). SnSchema B4c.",
        )?;
        self.add_recursive_def(
            "def minorsLam_eq_lamTel (fam : Name) (sig : ListType Nat) (body : KExpr) : forall (j : Nat), Eq KExpr (minorsLam fam j sig body) (lamTel (minorTys fam j sig) body) := ListType.rec Nat (fun (s : ListType Nat) => forall (j : Nat), Eq KExpr (minorsLam fam j s body) (lamTel (minorTys fam j s) body)) (fun (j : Nat) => Eq.refl KExpr body) (fun (r : Nat) (rest : ListType Nat) (ih : forall (j : Nat), Eq KExpr (minorsLam fam j rest body) (lamTel (minorTys fam j rest) body)) => fun (j : Nat) => Eq.cong KExpr KExpr (fun (Y : KExpr) => KExpr.lam (minorTy fam j r) Y) (minorsLam fam (Nat.add j (Nat.succ Nat.zero)) rest body) (lamTel (minorTys fam (Nat.add j (Nat.succ Nat.zero)) rest) body) (ih (Nat.add j (Nat.succ Nat.zero)))) sig",
            "minorsLam fam j sig body = lamTel (minorTys fam j sig) body (ListType.rec on sig; motive over j). SnSchema B4c.",
        )?;
        self.add_recursive_def(
            "def lamN_eq_lamTel (dom : KExpr) (r : Nat) (body : KExpr) : Eq KExpr (lamN dom r body) (lamTel (replicateLT r dom) body) := Nat.rec (fun (n : Nat) => Eq KExpr (lamN dom n body) (lamTel (replicateLT n dom) body)) (Eq.refl KExpr body) (fun (n : Nat) (ih : Eq KExpr (lamN dom n body) (lamTel (replicateLT n dom) body)) => Eq.cong KExpr KExpr (fun (Y : KExpr) => KExpr.lam dom Y) (lamN dom n body) (lamTel (replicateLT n dom) body) ih) r",
            "lamN dom r body = lamTel (replicateLT r dom) body (Nat.rec on r). SnSchema B4c.",
        )?;
        self.add_recursive_def(
            "def genRecRhs_eq_lamTel (fam : Name) (sig : ListType Nat) (u : Level) (j : Nat) (r : Nat) : Eq KExpr (genRecRhs fam sig u j r) (lamTel (genRecDoms fam sig u r) (genRecRhsBody fam sig u j r)) := Eq.cong KExpr KExpr (fun (Y : KExpr) => KExpr.lam (genMotiveTy fam u) Y) (minorsLam fam Nat.zero sig (lamN (famTypeC fam) r (genRecRhsBody fam sig u j r))) (lamTel (list_append (minorTys fam Nat.zero sig) (replicateLT r (famTypeC fam))) (genRecRhsBody fam sig u j r)) (Eq.trans KExpr (minorsLam fam Nat.zero sig (lamN (famTypeC fam) r (genRecRhsBody fam sig u j r))) (lamTel (minorTys fam Nat.zero sig) (lamTel (replicateLT r (famTypeC fam)) (genRecRhsBody fam sig u j r))) (lamTel (list_append (minorTys fam Nat.zero sig) (replicateLT r (famTypeC fam))) (genRecRhsBody fam sig u j r)) (Eq.trans KExpr (minorsLam fam Nat.zero sig (lamN (famTypeC fam) r (genRecRhsBody fam sig u j r))) (lamTel (minorTys fam Nat.zero sig) (lamN (famTypeC fam) r (genRecRhsBody fam sig u j r))) (lamTel (minorTys fam Nat.zero sig) (lamTel (replicateLT r (famTypeC fam)) (genRecRhsBody fam sig u j r))) (minorsLam_eq_lamTel fam sig (lamN (famTypeC fam) r (genRecRhsBody fam sig u j r)) Nat.zero) (Eq.cong KExpr KExpr (fun (Z : KExpr) => lamTel (minorTys fam Nat.zero sig) Z) (lamN (famTypeC fam) r (genRecRhsBody fam sig u j r)) (lamTel (replicateLT r (famTypeC fam)) (genRecRhsBody fam sig u j r)) (lamN_eq_lamTel (famTypeC fam) r (genRecRhsBody fam sig u j r)))) (Eq.symm KExpr (lamTel (list_append (minorTys fam Nat.zero sig) (replicateLT r (famTypeC fam))) (genRecRhsBody fam sig u j r)) (lamTel (minorTys fam Nat.zero sig) (lamTel (replicateLT r (famTypeC fam)) (genRecRhsBody fam sig u j r))) (lamTel_append (minorTys fam Nat.zero sig) (replicateLT r (famTypeC fam)) (genRecRhsBody fam sig u j r))))",
            "genRecRhs fam sig u j r = lamTel (genRecDoms fam sig u r) (genRecRhsBody fam sig u j r) (minorsLam/lamN_eq_lamTel + lamTel_append). SnSchema B4c.",
        )?;

        // ── B4c: apply_spine_append + list_append_length — leg-2 reshaping + the
        // lamTel_beta length precondition for genRecContract_steps.
        self.add_recursive_def(
            "def apply_spine_append (xs : ListType KExpr) (ys : ListType KExpr) : forall (h : KExpr), Eq KExpr (apply_spine (list_append xs ys) h) (apply_spine ys (apply_spine xs h)) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (h : KExpr), Eq KExpr (apply_spine (list_append l ys) h) (apply_spine ys (apply_spine l h))) (fun (h : KExpr) => Eq.refl KExpr (apply_spine ys h)) (fun (x : KExpr) (rest : ListType KExpr) (ih : forall (h : KExpr), Eq KExpr (apply_spine (list_append rest ys) h) (apply_spine ys (apply_spine rest h))) => fun (h : KExpr) => ih (KExpr.app h x)) xs",
            "apply_spine (list_append xs ys) h = apply_spine ys (apply_spine xs h) (ListType.rec on xs; motive over h). SnSchema B4c.",
        )?;
        self.add_recursive_def(
            "def list_append_length (xs : ListType KExpr) (ys : ListType KExpr) : Eq Nat (list_length (list_append xs ys)) (Nat.add (list_length xs) (list_length ys)) := ListType.rec KExpr (fun (l : ListType KExpr) => Eq Nat (list_length (list_append l ys)) (Nat.add (list_length l) (list_length ys))) (Eq.symm Nat (Nat.add Nat.zero (list_length ys)) (list_length ys) (nat_zero_add (list_length ys))) (fun (x : KExpr) (rest : ListType KExpr) (ih : Eq Nat (list_length (list_append rest ys)) (Nat.add (list_length rest) (list_length ys))) => Eq.trans Nat (Nat.succ (list_length (list_append rest ys))) (Nat.succ (Nat.add (list_length rest) (list_length ys))) (Nat.add (Nat.succ (list_length rest)) (list_length ys)) (Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (list_length (list_append rest ys)) (Nat.add (list_length rest) (list_length ys)) ih) (Eq.symm Nat (Nat.add (Nat.succ (list_length rest)) (list_length ys)) (Nat.succ (Nat.add (list_length rest) (list_length ys))) (nat_succ_add (list_length rest) (list_length ys)))) xs",
            "list_length (list_append xs ys) = list_length xs + list_length ys (ListType.rec on xs; nat_zero_add/nat_succ_add). SnSchema B4c.",
        )?;

        // ── B4c crux, structural tier: instIter distributes over app/const/apply_spine,
        // mapLT over append/length, bvarSeq length. Pure structural/definitional
        // inductions — no propositional `<`, no arithmetic side-conditions. These are
        // the load-bearing distribution lemmas for genRecRhs_instIter.
        self.add_recursive_def(
            "def mapLT_length (f : KExpr -> KExpr) (xs : ListType KExpr) : Eq Nat (list_length (mapLT f xs)) (list_length xs) := ListType.rec KExpr (fun (l : ListType KExpr) => Eq Nat (list_length (mapLT f l)) (list_length l)) (Eq.refl Nat Nat.zero) (fun (x : KExpr) (rest : ListType KExpr) (ih : Eq Nat (list_length (mapLT f rest)) (list_length rest)) => Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (list_length (mapLT f rest)) (list_length rest) ih) xs",
            "list_length (mapLT f xs) = list_length xs (ListType.rec on xs). SnSchema B4c crux.",
        )?;
        self.add_recursive_def(
            "def instIter_app (args : ListType KExpr) : forall (f : KExpr) (a : KExpr), Eq KExpr (instIter (KExpr.app f a) args) (KExpr.app (instIter f args) (instIter a args)) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (f : KExpr) (a : KExpr), Eq KExpr (instIter (KExpr.app f a) l) (KExpr.app (instIter f l) (instIter a l))) (fun (f : KExpr) (a : KExpr) => Eq.refl KExpr (KExpr.app f a)) (fun (x : KExpr) (rest : ListType KExpr) (ih : forall (f : KExpr) (a : KExpr), Eq KExpr (instIter (KExpr.app f a) rest) (KExpr.app (instIter f rest) (instIter a rest))) => fun (f : KExpr) (a : KExpr) => ih (instantiate_at f x (list_length rest)) (instantiate_at a x (list_length rest))) args",
            "instIter (app f a) args = app (instIter f args) (instIter a args) (ListType.rec on args; instantiate_at distributes over app). SnSchema B4c crux.",
        )?;
        self.add_recursive_def(
            "def instIter_const (args : ListType KExpr) : forall (c : Name) (us : ListType Level), Eq KExpr (instIter (KExpr.const c us) args) (KExpr.const c us) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (c : Name) (us : ListType Level), Eq KExpr (instIter (KExpr.const c us) l) (KExpr.const c us)) (fun (c : Name) (us : ListType Level) => Eq.refl KExpr (KExpr.const c us)) (fun (x : KExpr) (rest : ListType KExpr) (ih : forall (c : Name) (us : ListType Level), Eq KExpr (instIter (KExpr.const c us) rest) (KExpr.const c us)) => fun (c : Name) (us : ListType Level) => ih c us) args",
            "instIter (const c us) args = const c us (ListType.rec on args; const inert under instantiate_at). SnSchema B4c crux.",
        )?;
        self.add_recursive_def(
            "def instIter_apply_spine (xs : ListType KExpr) : forall (h : KExpr) (args : ListType KExpr), Eq KExpr (instIter (apply_spine xs h) args) (apply_spine (mapLT (fun (t : KExpr) => instIter t args) xs) (instIter h args)) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (h : KExpr) (args : ListType KExpr), Eq KExpr (instIter (apply_spine l h) args) (apply_spine (mapLT (fun (t : KExpr) => instIter t args) l) (instIter h args))) (fun (h : KExpr) (args : ListType KExpr) => Eq.refl KExpr (instIter h args)) (fun (x : KExpr) (rest : ListType KExpr) (ih : forall (h : KExpr) (args : ListType KExpr), Eq KExpr (instIter (apply_spine rest h) args) (apply_spine (mapLT (fun (t : KExpr) => instIter t args) rest) (instIter h args))) => fun (h : KExpr) (args : ListType KExpr) => Eq.trans KExpr (instIter (apply_spine rest (KExpr.app h x)) args) (apply_spine (mapLT (fun (t : KExpr) => instIter t args) rest) (instIter (KExpr.app h x) args)) (apply_spine (mapLT (fun (t : KExpr) => instIter t args) rest) (KExpr.app (instIter h args) (instIter x args))) (ih (KExpr.app h x) args) (Eq.cong KExpr KExpr (fun (Y : KExpr) => apply_spine (mapLT (fun (t : KExpr) => instIter t args) rest) Y) (instIter (KExpr.app h x) args) (KExpr.app (instIter h args) (instIter x args)) (instIter_app args h x))) xs",
            "instIter (apply_spine xs h) args = apply_spine (mapLT (instIter . args) xs) (instIter h args) (ListType.rec on xs; instIter_app). SnSchema B4c crux.",
        )?;
        self.add_recursive_def(
            "def mapLT_append (f : KExpr -> KExpr) (xs : ListType KExpr) : forall (ys : ListType KExpr), Eq (ListType KExpr) (mapLT f (list_append xs ys)) (list_append (mapLT f xs) (mapLT f ys)) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (ys : ListType KExpr), Eq (ListType KExpr) (mapLT f (list_append l ys)) (list_append (mapLT f l) (mapLT f ys))) (fun (ys : ListType KExpr) => Eq.refl (ListType KExpr) (mapLT f ys)) (fun (x : KExpr) (rest : ListType KExpr) (ih : forall (ys : ListType KExpr), Eq (ListType KExpr) (mapLT f (list_append rest ys)) (list_append (mapLT f rest) (mapLT f ys))) => fun (ys : ListType KExpr) => Eq.cong (ListType KExpr) (ListType KExpr) (fun (Z : ListType KExpr) => ListType.cons KExpr (f x) Z) (mapLT f (list_append rest ys)) (list_append (mapLT f rest) (mapLT f ys)) (ih ys)) xs",
            "mapLT f (xs ++ ys) = mapLT f xs ++ mapLT f ys (ListType.rec on xs). SnSchema B4c crux.",
        )?;
        self.add_recursive_def(
            "def bvarSeq_length (n : Nat) : forall (top : Nat), Eq Nat (list_length (bvarSeq top n)) n := Nat.rec (fun (k : Nat) => forall (top : Nat), Eq Nat (list_length (bvarSeq top k)) k) (fun (top : Nat) => Eq.refl Nat Nat.zero) (fun (n0 : Nat) (ih : forall (top : Nat), Eq Nat (list_length (bvarSeq top n0)) n0) => fun (top : Nat) => Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (list_length (bvarSeq (Nat.sub top (Nat.succ Nat.zero)) n0)) n0 (ih (Nat.sub top (Nat.succ Nat.zero)))) n",
            "list_length (bvarSeq top n) = n (Nat.rec on n, top varies). SnSchema B4c crux.",
        )?;

        // ── B4c crux, list-lookup tier (boolean `<` encoding). We use the
        // computational nat_lt_b (Eq Bool = true) rather than the Lt inductive:
        // nat_lt_b (succ a)(succ b) reduces to nat_lt_b a b by rfl, so
        // "lt_of_succ_lt_succ"/"not_lt_zero" are DEFINITIONAL, dodging inductive
        // inversion. bool_true_ne_false discharges the nil-length contradiction.
        self.add_recursive_def(
            "def bool_true_ne_false (C : Type) (h : Eq Bool Bool.true Bool.false) : C := Eq.substType Bool (fun (b : Bool) => Bool.rec (fun (_ : Bool) => Type) C Nat b) Bool.true Bool.false h Nat.zero",
            "Eq Bool true false -> C (Bool.rec motive: false-branch C, true-branch Nat inhabited by zero; Type-level to avoid Prop/Type universe clash). SnSchema B4c crux.",
        )?;
        self.add_recursive_def(
            "def nat_lt_zero_false (q : Nat) : Eq Bool (nat_lt_b q Nat.zero) Bool.false := Nat.rec (fun (k : Nat) => Eq Bool (nat_lt_b k Nat.zero) Bool.false) (Eq.refl Bool Bool.false) (fun (q0 : Nat) (ih : Eq Bool (nat_lt_b q0 Nat.zero) Bool.false) => Eq.refl Bool Bool.false) q",
            "nat_lt_b q 0 = false for all q (Nat.rec on q; both branches rfl). SnSchema B4c crux.",
        )?;
        self.add_recursive_def(
            "def listGet_mapLT (f : KExpr -> KExpr) (xs : ListType KExpr) : forall (p : Nat) (x : KExpr), Eq (OptionType KExpr) (listGet xs p) (OptionType.some KExpr x) -> Eq (OptionType KExpr) (listGet (mapLT f xs) p) (OptionType.some KExpr (f x)) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (p : Nat) (x : KExpr), Eq (OptionType KExpr) (listGet l p) (OptionType.some KExpr x) -> Eq (OptionType KExpr) (listGet (mapLT f l) p) (OptionType.some KExpr (f x))) (fun (p : Nat) (x : KExpr) (h : Eq (OptionType KExpr) (listGet (ListType.nil KExpr) p) (OptionType.some KExpr x)) => option_none_ne_some KExpr x (Eq (OptionType KExpr) (listGet (mapLT f (ListType.nil KExpr)) p) (OptionType.some KExpr (f x))) h) (fun (a : KExpr) (rest : ListType KExpr) (ih : forall (p : Nat) (x : KExpr), Eq (OptionType KExpr) (listGet rest p) (OptionType.some KExpr x) -> Eq (OptionType KExpr) (listGet (mapLT f rest) p) (OptionType.some KExpr (f x))) => fun (p : Nat) => Nat.rec (fun (pp : Nat) => forall (x : KExpr), Eq (OptionType KExpr) (listGet (ListType.cons KExpr a rest) pp) (OptionType.some KExpr x) -> Eq (OptionType KExpr) (listGet (mapLT f (ListType.cons KExpr a rest)) pp) (OptionType.some KExpr (f x))) (fun (x : KExpr) (h : Eq (OptionType KExpr) (listGet (ListType.cons KExpr a rest) Nat.zero) (OptionType.some KExpr x)) => Eq.cong KExpr (OptionType KExpr) (fun (w : KExpr) => OptionType.some KExpr (f w)) a x (option_some_inj KExpr a x h)) (fun (p0 : Nat) (_ : forall (x : KExpr), Eq (OptionType KExpr) (listGet (ListType.cons KExpr a rest) p0) (OptionType.some KExpr x) -> Eq (OptionType KExpr) (listGet (mapLT f (ListType.cons KExpr a rest)) p0) (OptionType.some KExpr (f x))) => fun (x : KExpr) (h : Eq (OptionType KExpr) (listGet (ListType.cons KExpr a rest) (Nat.succ p0)) (OptionType.some KExpr x)) => ih p0 x h) p) xs",
            "listGet xs p = some x -> listGet (mapLT f xs) p = some (f x) (ListType.rec on xs, Nat.rec on p). SnSchema B4c crux.",
        )?;
        // ── B4c crux, boolean-< lookup tier: listGet on append below the split,
        // and bvarSeq's descending-index lookup. nat_sub_pred_comm bridges
        // (top-1)-j = top-(succ j) for bvarSeq_listGet's recursive index.
        // Reduction-refl helpers: standalone `Eq.refl` proofs of one-step
        // recursor firings. The elaborator's DIRECT conversion check reduces
        // these (constructor-headed majors), but its UNIFICATION defeq does NOT
        // reduce a nested-recursor-def form to match an expected type. So the
        // technique for the whole crux: bridge every reduction through these
        // refl-lemmas + explicit Eq.trans, never letting the elaborator unify
        // two different-form nested-recursor-def applications.
        self.add_recursive_def(
            "def listGet_cons_succ (a : KExpr) (T : ListType KExpr) (k : Nat) : Eq (OptionType KExpr) (listGet (ListType.cons KExpr a T) (Nat.succ k)) (listGet T k) := Eq.refl (OptionType KExpr) (listGet T k)",
            "listGet (cons a T) (succ k) = listGet T k (standalone refl; direct-conversion reduces it). SnSchema B4c crux.",
        )?;
        self.add_recursive_def(
            "def nat_lt_b_succ_succ (a : Nat) (b : Nat) : Eq Bool (nat_lt_b (Nat.succ a) (Nat.succ b)) (nat_lt_b a b) := Eq.refl Bool (nat_lt_b a b)",
            "nat_lt_b (succ a) (succ b) = nat_lt_b a b (standalone refl). SnSchema B4c crux.",
        )?;
        // NOTE: listGet_append_lt / listGet_append_ge / bvarSeq_listGet DEFERRED.
        // They require the elaborator to reconcile two applications of a nested-
        // recursor def (listGet / nat_lt_b) whose args differ but are defeq. Clean's
        // UNIFICATION defeq refuses this (fails "expected Bool/Nat, Discriminant 6
        // vs 3") even when every recursor major is constructor-headed and even when
        // bridged via nat_lt_b_succ_succ + listGet_cons_succ + Eq.trans/substType.
        // The standalone refl helpers above DO pass (direct conversion), so the peel
        // reductions are individually fine — the blocker is purely unification-side.
        // UPDATE: the second strategy was taken. Lookup was reformulated ~70 lines
        // below in this same stage as `lget` (ListType.rec on the LIST; the index is
        // handled by nat_is_zero / Nat.pred / Bool.rec — no nested Nat.rec under a
        // function motive), and the three lemmas landed there as lget_append_lt /
        // lget_append_ge / bvarSeq_lget, all load-bearing: lget_append_ge in
        // instIter_bvar_field, bvarSeq_lget in mapLT_instIter_fields, lget_append_lt
        // in genRecRhs_instIter. The listGet-flavoured formulations stay unported and
        // the Discriminant 6-vs-3 elaborator issue is still un-root-caused. See memory
        // clean-snschema-rung-progress.
        self.add_recursive_def(
            "def nat_sub_pred_comm (top : Nat) : forall (j : Nat), Eq Nat (Nat.sub (Nat.pred top) j) (Nat.pred (Nat.sub top j)) := Nat.rec (fun (k : Nat) => Eq Nat (Nat.sub (Nat.pred top) k) (Nat.pred (Nat.sub top k))) (Eq.refl Nat (Nat.pred top)) (fun (j0 : Nat) (ih : Eq Nat (Nat.sub (Nat.pred top) j0) (Nat.pred (Nat.sub top j0))) => Eq.cong Nat Nat (fun (w : Nat) => Nat.pred w) (Nat.sub (Nat.pred top) j0) (Nat.pred (Nat.sub top j0)) ih)",
            "(pred top) - j = pred (top - j) (Nat.rec on j, no trailing major -> forall j; Nat.sub recurses on 2nd arg via pred). SnSchema B4c crux.",
        )?;

        // ── B4c crux, OPTION-B experiment: lookup via list_head o list_drop (both
        // SINGLE recursors) instead of the nested-recursor listGet, so the append
        // fact is a one-line Eq.cong over the already-green list_drop_append_gen —
        // no nested-recursor-def unification. If this censuses green, the whole
        // lookup tier reformulates onto lookupHD.
        self.add_recursive_def(
            "def lookupHD (i : Nat) (xs : ListType KExpr) : OptionType KExpr := list_head (list_drop i xs)",
            "lookupHD i xs = list_head (list_drop i xs) (single-recursor lookup, option-B). SnSchema B4c crux.",
        )?;
        self.add_recursive_def(
            "def lookupHD_append_ge (xs : ListType KExpr) (ys : ListType KExpr) (q : Nat) : Eq (OptionType KExpr) (lookupHD (Nat.add (list_length xs) q) (list_append xs ys)) (lookupHD q ys) := Eq.cong (ListType KExpr) (OptionType KExpr) list_head (list_drop (Nat.add (list_length xs) q) (list_append xs ys)) (list_drop q ys) (list_drop_append_gen xs q ys)",
            "lookupHD (|xs| + q) (xs ++ ys) = lookupHD q ys — one-line Eq.cong list_head over green list_drop_append_gen; NO nested-recursor comparison. SnSchema B4c crux (option-B validation).",
        )?;

        // ── B4c crux, lookupHD tier (option-B): nil, mapLT-lift, append-below-split.
        self.add_recursive_def(
            "def lookupHD_nil (i : Nat) : Eq (OptionType KExpr) (lookupHD i (ListType.nil KExpr)) (OptionType.none KExpr) := Eq.trans (OptionType KExpr) (lookupHD i (ListType.nil KExpr)) (list_head (ListType.nil KExpr)) (OptionType.none KExpr) (Eq.cong (ListType KExpr) (OptionType KExpr) list_head (list_drop i (ListType.nil KExpr)) (ListType.nil KExpr) (list_drop_nil i)) (Eq.refl (OptionType KExpr) (OptionType.none KExpr))",
            "lookupHD i [] = none (Eq.cong list_head over green list_drop_nil, then list_head [] = none). SnSchema B4c crux (option-B).",
        )?;
        self.add_recursive_def(
            "def list_tail_mapLT (f : KExpr -> KExpr) (L : ListType KExpr) : Eq (ListType KExpr) (list_tail (mapLT f L)) (mapLT f (list_tail L)) := ListType.rec KExpr (fun (l : ListType KExpr) => Eq (ListType KExpr) (list_tail (mapLT f l)) (mapLT f (list_tail l))) (Eq.refl (ListType KExpr) (ListType.nil KExpr)) (fun (a : KExpr) (rest : ListType KExpr) (ih : Eq (ListType KExpr) (list_tail (mapLT f rest)) (mapLT f (list_tail rest))) => Eq.refl (ListType KExpr) (mapLT f rest)) L",
            "list_tail (mapLT f L) = mapLT f (list_tail L) (ListType.rec on L; both cases refl). SnSchema B4c helper.",
        )?;
        self.add_recursive_def(
            "def list_head_mapLT (f : KExpr -> KExpr) (L : ListType KExpr) (a : KExpr) (hL : Eq (OptionType KExpr) (list_head L) (OptionType.some KExpr a)) : Eq (OptionType KExpr) (list_head (mapLT f L)) (OptionType.some KExpr (f a)) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (a0 : KExpr), Eq (OptionType KExpr) (list_head l) (OptionType.some KExpr a0) -> Eq (OptionType KExpr) (list_head (mapLT f l)) (OptionType.some KExpr (f a0))) (fun (a0 : KExpr) (hnil : Eq (OptionType KExpr) (list_head (ListType.nil KExpr)) (OptionType.some KExpr a0)) => option_none_ne_some KExpr a0 (Eq (OptionType KExpr) (list_head (mapLT f (ListType.nil KExpr))) (OptionType.some KExpr (f a0))) hnil) (fun (b0 : KExpr) (rest : ListType KExpr) (ih : forall (a0 : KExpr), Eq (OptionType KExpr) (list_head rest) (OptionType.some KExpr a0) -> Eq (OptionType KExpr) (list_head (mapLT f rest)) (OptionType.some KExpr (f a0))) => fun (a0 : KExpr) (hc : Eq (OptionType KExpr) (list_head (ListType.cons KExpr b0 rest)) (OptionType.some KExpr a0)) => Eq.cong KExpr (OptionType KExpr) (fun (w : KExpr) => OptionType.some KExpr (f w)) b0 a0 (option_some_inj KExpr b0 a0 hc)) L a hL",
            "list_head L = some a -> list_head (mapLT f L) = some (f a) (ListType.rec on L; nil absurd, cons via option_some_inj + Eq.cong). SnSchema B4c helper.",
        )?;
        self.add_recursive_def(
            "def lookupHD_mapLT (f : KExpr -> KExpr) (xs : ListType KExpr) (p : Nat) (x : KExpr) (h : Eq (OptionType KExpr) (lookupHD p xs) (OptionType.some KExpr x)) : Eq (OptionType KExpr) (lookupHD p (mapLT f xs)) (OptionType.some KExpr (f x)) := Nat.rec (fun (pp : Nat) => forall (L : ListType KExpr) (y : KExpr), Eq (OptionType KExpr) (lookupHD pp L) (OptionType.some KExpr y) -> Eq (OptionType KExpr) (lookupHD pp (mapLT f L)) (OptionType.some KExpr (f y))) (fun (L : ListType KExpr) (y : KExpr) (hz : Eq (OptionType KExpr) (lookupHD Nat.zero L) (OptionType.some KExpr y)) => list_head_mapLT f L y hz) (fun (m : Nat) (ih : forall (L : ListType KExpr) (y : KExpr), Eq (OptionType KExpr) (lookupHD m L) (OptionType.some KExpr y) -> Eq (OptionType KExpr) (lookupHD m (mapLT f L)) (OptionType.some KExpr (f y))) => fun (L : ListType KExpr) (y : KExpr) (hs : Eq (OptionType KExpr) (lookupHD (Nat.succ m) L) (OptionType.some KExpr y)) => Eq.trans (OptionType KExpr) (lookupHD (Nat.succ m) (mapLT f L)) (lookupHD m (mapLT f (list_tail L))) (OptionType.some KExpr (f y)) (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (Z : ListType KExpr) => lookupHD m Z) (list_tail (mapLT f L)) (mapLT f (list_tail L)) (list_tail_mapLT f L)) (ih (list_tail L) y hs)) p xs x h",
            "lookupHD p xs = some x -> lookupHD p (mapLT f xs) = some (f x) (Nat.rec on p param; base list_head_mapLT, step peels succ + list_tail_mapLT commute + ih). SnSchema B4c crux (option-B).",
        )?;
        self.add_recursive_def(
            "def lookupHD_cons_succ (a : KExpr) (T : ListType KExpr) (m : Nat) : Eq (OptionType KExpr) (lookupHD (Nat.succ m) (ListType.cons KExpr a T)) (lookupHD m T) := Eq.refl (OptionType KExpr) (lookupHD m T)",
            "lookupHD (succ m) (cons a T) = lookupHD m T (standalone refl; the list_drop-succ peel done at PARAM level so callers never fire list_drop on a bvar-succ). SnSchema B4c crux (option-B).",
        )?;
        // ── B4c crux: list_head_append + lookupHD_append_lt (option-existence
        // hypothesis, forall-ABSTRACT list in the Nat.rec-on-index motive, inner
        // ListType.rec destructure of L in the succ body — mirrors green lookupHD_mapLT
        // so list_drop's major-var is never a bvar with a concrete list).
        self.add_recursive_def(
            "def list_head_append (ys : ListType KExpr) (L : ListType KExpr) : forall (w : KExpr), Eq (OptionType KExpr) (list_head L) (OptionType.some KExpr w) -> Eq (OptionType KExpr) (list_head (list_append L ys)) (OptionType.some KExpr w) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (w : KExpr), Eq (OptionType KExpr) (list_head l) (OptionType.some KExpr w) -> Eq (OptionType KExpr) (list_head (list_append l ys)) (OptionType.some KExpr w)) (fun (w : KExpr) (hn : Eq (OptionType KExpr) (list_head (ListType.nil KExpr)) (OptionType.some KExpr w)) => option_none_ne_some KExpr w (Eq (OptionType KExpr) (list_head (list_append (ListType.nil KExpr) ys)) (OptionType.some KExpr w)) hn) (fun (a : KExpr) (T : ListType KExpr) (ih : forall (w : KExpr), Eq (OptionType KExpr) (list_head T) (OptionType.some KExpr w) -> Eq (OptionType KExpr) (list_head (list_append T ys)) (OptionType.some KExpr w)) => fun (w : KExpr) (hc : Eq (OptionType KExpr) (list_head (ListType.cons KExpr a T)) (OptionType.some KExpr w)) => Eq.cong KExpr (OptionType KExpr) (fun (z : KExpr) => OptionType.some KExpr z) a w (option_some_inj KExpr a w hc)) L",
            "list_head L = some w -> list_head (L ++ ys) = some w (ListType.rec on L; nil absurd, cons head preserved). SnSchema B4c crux.",
        )?;

        // ── B4c crux, THE STRUCTURALLY BUG-IMMUNE LOOKUP: `lget xs i`. Recurses on
        // the LIST (ListType.rec — major is the list, NEVER a bvar-index), and
        // handles the index with NON-function-motive ops: nat_is_zero (Nat.rec ->
        // Bool), Nat.pred (Nat.rec -> Nat), Bool.rec (-> OptionType). No list_drop
        // (dodges the function-motive bvar-major bug B), no inner Nat.rec-in-a-
        // function-motive (dodges the nested-recursor unification bug A). BONUS:
        // lget nil i == none DEFINITIONALLY for any i (base ignores i).
        self.add_recursive_def(
            "def lget (xs : ListType KExpr) (i : Nat) : OptionType KExpr := ListType.rec KExpr (fun (_ : ListType KExpr) => Nat -> OptionType KExpr) (fun (j : Nat) => OptionType.none KExpr) (fun (a : KExpr) (T : ListType KExpr) (ih : Nat -> OptionType KExpr) => fun (j : Nat) => Bool.rec (fun (_ : Bool) => OptionType KExpr) (ih (Nat.pred j)) (OptionType.some KExpr a) (nat_is_zero j)) xs i",
            "lget xs i = list lookup at index i (ListType.rec on xs; index via nat_is_zero/Nat.pred/Bool.rec, all non-function motives). Structurally dodges both elaborator defeq bugs. SnSchema B4c crux.",
        )?;
        self.add_recursive_def(
            "def lget_append_lt (ys : ListType KExpr) (xs : ListType KExpr) : forall (q : Nat) (v : KExpr), Eq (OptionType KExpr) (lget xs q) (OptionType.some KExpr v) -> Eq (OptionType KExpr) (lget (list_append xs ys) q) (OptionType.some KExpr v) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (q : Nat) (v : KExpr), Eq (OptionType KExpr) (lget l q) (OptionType.some KExpr v) -> Eq (OptionType KExpr) (lget (list_append l ys) q) (OptionType.some KExpr v)) (fun (q : Nat) (v : KExpr) (h : Eq (OptionType KExpr) (lget (ListType.nil KExpr) q) (OptionType.some KExpr v)) => option_none_ne_some KExpr v (Eq (OptionType KExpr) (lget (list_append (ListType.nil KExpr) ys) q) (OptionType.some KExpr v)) h) (fun (a : KExpr) (T : ListType KExpr) (ih : forall (q : Nat) (v : KExpr), Eq (OptionType KExpr) (lget T q) (OptionType.some KExpr v) -> Eq (OptionType KExpr) (lget (list_append T ys) q) (OptionType.some KExpr v)) => fun (q : Nat) (v : KExpr) => Bool.rec (fun (b : Bool) => Eq (OptionType KExpr) (Bool.rec (fun (_ : Bool) => OptionType KExpr) (lget T (Nat.pred q)) (OptionType.some KExpr a) b) (OptionType.some KExpr v) -> Eq (OptionType KExpr) (Bool.rec (fun (_ : Bool) => OptionType KExpr) (lget (list_append T ys) (Nat.pred q)) (OptionType.some KExpr a) b) (OptionType.some KExpr v)) (fun (hf : Eq (OptionType KExpr) (lget T (Nat.pred q)) (OptionType.some KExpr v)) => ih (Nat.pred q) v hf) (fun (ht : Eq (OptionType KExpr) (OptionType.some KExpr a) (OptionType.some KExpr v)) => ht) (nat_is_zero q)) xs",
            "lget xs q = some v -> lget (xs ++ ys) q = some v. ListType.rec on xs; cons case cases nat_is_zero q via Bool.rec (true->head refl, false->ih at pred q). No list_drop, no bvar-index major. SnSchema B4c crux (lget).",
        )?;
        self.add_recursive_def(
            "def lget_cons_succ (a : KExpr) (T : ListType KExpr) (m : Nat) : Eq (OptionType KExpr) (lget (ListType.cons KExpr a T) (Nat.succ m)) (lget T m) := Eq.refl (OptionType KExpr) (lget T m)",
            "lget (cons a T) (succ m) = lget T m (standalone refl; nat_is_zero (succ m)=false, pred (succ m)=m). SnSchema B4c crux (lget).",
        )?;
        self.add_recursive_def(
            "def lget_cons_zero (a : KExpr) (T : ListType KExpr) : Eq (OptionType KExpr) (lget (ListType.cons KExpr a T) Nat.zero) (OptionType.some KExpr a) := Eq.refl (OptionType KExpr) (OptionType.some KExpr a)",
            "lget (cons a T) 0 = some a (standalone refl; nat_is_zero 0 = true -> Bool.rec true -> some a). SnSchema B4c crux (lget).",
        )?;
        // Prop-landing `0 = succ a` absurdity (library nat_zero_ne_succ takes C:Type,
        // incompatible with a Prop goal like `Eq (ListType KExpr) ..`). Nat.rec large
        // elim into Prop: D n = (n=0 ? `0=0` : C); transport refl:D 0 along h to D(succ a)=C.
        self.add_recursive_def(
            "def nat_zero_ne_succ_prop (a : Nat) (C : Prop) (h : Eq Nat Nat.zero (Nat.succ a)) : C := Eq.substType Nat (fun (n : Nat) => Nat.rec (fun (_ : Nat) => Prop) (Eq Nat Nat.zero Nat.zero) (fun (k : Nat) (_ : Prop) => C) n) Nat.zero (Nat.succ a) h (Eq.refl Nat Nat.zero)",
            "Eq 0 (succ a) -> C for C:Prop (Nat.rec large-elim CPS; D 0 = (0=0) inhabited by refl, D (succ a) = C). SnSchema B4c helper.",
        )?;
        // lget-based list extensionality: two lists with equal length and equal
        // lget at every in-range index are equal. Double ListType.rec (outer xs,
        // inner ys). Absurd length cases bridge hlen through list_length_nil /
        // list_length_cons EXPLICITLY (never rely on list_length iota in
        // arg-unification). cons/cons: head via option_some_inj (lget..0 peeled by
        // lget_cons_zero), tail via ihx; the Lt args to hget are substType-pinned
        // to `list_length (cons ..)` via list_length_cons so the weak unifier never
        // has to fire the iota. Gateway to mapLT_instIter_fields. Guide listGet_ext.
        self.add_recursive_def(
            "def lget_ext (xs : ListType KExpr) : forall (ys : ListType KExpr), Eq Nat (list_length xs) (list_length ys) -> (forall (p : Nat), Lt p (list_length xs) -> Eq (OptionType KExpr) (lget xs p) (lget ys p)) -> Eq (ListType KExpr) xs ys := ListType.rec KExpr (fun (l : ListType KExpr) => forall (ys : ListType KExpr), Eq Nat (list_length l) (list_length ys) -> (forall (p : Nat), Lt p (list_length l) -> Eq (OptionType KExpr) (lget l p) (lget ys p)) -> Eq (ListType KExpr) l ys) (fun (ys : ListType KExpr) => ListType.rec KExpr (fun (yl : ListType KExpr) => Eq Nat (list_length (ListType.nil KExpr)) (list_length yl) -> (forall (p : Nat), Lt p (list_length (ListType.nil KExpr)) -> Eq (OptionType KExpr) (lget (ListType.nil KExpr) p) (lget yl p)) -> Eq (ListType KExpr) (ListType.nil KExpr) yl) (fun (hlen : Eq Nat (list_length (ListType.nil KExpr)) (list_length (ListType.nil KExpr))) (hget : forall (p : Nat), Lt p (list_length (ListType.nil KExpr)) -> Eq (OptionType KExpr) (lget (ListType.nil KExpr) p) (lget (ListType.nil KExpr) p)) => Eq.refl (ListType KExpr) (ListType.nil KExpr)) (fun (y : KExpr) (ys' : ListType KExpr) (_ihy : Eq Nat (list_length (ListType.nil KExpr)) (list_length ys') -> (forall (p : Nat), Lt p (list_length (ListType.nil KExpr)) -> Eq (OptionType KExpr) (lget (ListType.nil KExpr) p) (lget ys' p)) -> Eq (ListType KExpr) (ListType.nil KExpr) ys') (hlen : Eq Nat (list_length (ListType.nil KExpr)) (list_length (ListType.cons KExpr y ys'))) (hget : forall (p : Nat), Lt p (list_length (ListType.nil KExpr)) -> Eq (OptionType KExpr) (lget (ListType.nil KExpr) p) (lget (ListType.cons KExpr y ys') p)) => nat_zero_ne_succ_prop (list_length ys') (Eq (ListType KExpr) (ListType.nil KExpr) (ListType.cons KExpr y ys')) (Eq.trans Nat Nat.zero (list_length (ListType.cons KExpr y ys')) (Nat.succ (list_length ys')) (Eq.trans Nat Nat.zero (list_length (ListType.nil KExpr)) (list_length (ListType.cons KExpr y ys')) (Eq.symm Nat (list_length (ListType.nil KExpr)) Nat.zero list_length_nil) hlen) (list_length_cons y ys'))) ys) (fun (x : KExpr) (xs' : ListType KExpr) (ihx : forall (ys : ListType KExpr), Eq Nat (list_length xs') (list_length ys) -> (forall (p : Nat), Lt p (list_length xs') -> Eq (OptionType KExpr) (lget xs' p) (lget ys p)) -> Eq (ListType KExpr) xs' ys) => fun (ys : ListType KExpr) => ListType.rec KExpr (fun (yl : ListType KExpr) => Eq Nat (list_length (ListType.cons KExpr x xs')) (list_length yl) -> (forall (p : Nat), Lt p (list_length (ListType.cons KExpr x xs')) -> Eq (OptionType KExpr) (lget (ListType.cons KExpr x xs') p) (lget yl p)) -> Eq (ListType KExpr) (ListType.cons KExpr x xs') yl) (fun (hlen : Eq Nat (list_length (ListType.cons KExpr x xs')) (list_length (ListType.nil KExpr))) (hget : forall (p : Nat), Lt p (list_length (ListType.cons KExpr x xs')) -> Eq (OptionType KExpr) (lget (ListType.cons KExpr x xs') p) (lget (ListType.nil KExpr) p)) => nat_zero_ne_succ_prop (list_length xs') (Eq (ListType KExpr) (ListType.cons KExpr x xs') (ListType.nil KExpr)) (Eq.symm Nat (Nat.succ (list_length xs')) Nat.zero (Eq.trans Nat (Nat.succ (list_length xs')) (list_length (ListType.cons KExpr x xs')) Nat.zero (Eq.symm Nat (list_length (ListType.cons KExpr x xs')) (Nat.succ (list_length xs')) (list_length_cons x xs')) (Eq.trans Nat (list_length (ListType.cons KExpr x xs')) (list_length (ListType.nil KExpr)) Nat.zero hlen list_length_nil)))) (fun (y : KExpr) (ys' : ListType KExpr) (_ihy : Eq Nat (list_length (ListType.cons KExpr x xs')) (list_length ys') -> (forall (p : Nat), Lt p (list_length (ListType.cons KExpr x xs')) -> Eq (OptionType KExpr) (lget (ListType.cons KExpr x xs') p) (lget ys' p)) -> Eq (ListType KExpr) (ListType.cons KExpr x xs') ys') (hlen : Eq Nat (list_length (ListType.cons KExpr x xs')) (list_length (ListType.cons KExpr y ys'))) (hget : forall (p : Nat), Lt p (list_length (ListType.cons KExpr x xs')) -> Eq (OptionType KExpr) (lget (ListType.cons KExpr x xs') p) (lget (ListType.cons KExpr y ys') p)) => Eq.trans (ListType KExpr) (ListType.cons KExpr x xs') (ListType.cons KExpr y xs') (ListType.cons KExpr y ys') (Eq.cong KExpr (ListType KExpr) (fun (z : KExpr) => ListType.cons KExpr z xs') x y (option_some_inj KExpr x y (Eq.trans (OptionType KExpr) (OptionType.some KExpr x) (lget (ListType.cons KExpr y ys') Nat.zero) (OptionType.some KExpr y) (Eq.trans (OptionType KExpr) (OptionType.some KExpr x) (lget (ListType.cons KExpr x xs') Nat.zero) (lget (ListType.cons KExpr y ys') Nat.zero) (Eq.symm (OptionType KExpr) (lget (ListType.cons KExpr x xs') Nat.zero) (OptionType.some KExpr x) (lget_cons_zero x xs')) (hget Nat.zero (Eq.substType Nat (fun (N : Nat) => Lt Nat.zero N) (Nat.succ (list_length xs')) (list_length (ListType.cons KExpr x xs')) (Eq.symm Nat (list_length (ListType.cons KExpr x xs')) (Nat.succ (list_length xs')) (list_length_cons x xs')) (Lt.zero_lt_succ (list_length xs'))))) (lget_cons_zero y ys')))) (Eq.cong (ListType KExpr) (ListType KExpr) (fun (L : ListType KExpr) => ListType.cons KExpr y L) xs' ys' (ihx ys' (nat_succ_inj (list_length xs') (list_length ys') (Eq.trans Nat (Nat.succ (list_length xs')) (list_length (ListType.cons KExpr y ys')) (Nat.succ (list_length ys')) (Eq.trans Nat (Nat.succ (list_length xs')) (list_length (ListType.cons KExpr x xs')) (list_length (ListType.cons KExpr y ys')) (Eq.symm Nat (list_length (ListType.cons KExpr x xs')) (Nat.succ (list_length xs')) (list_length_cons x xs')) hlen) (list_length_cons y ys'))) (fun (p : Nat) (hp : Lt p (list_length xs')) => Eq.trans (OptionType KExpr) (lget xs' p) (lget (ListType.cons KExpr y ys') (Nat.succ p)) (lget ys' p) (Eq.trans (OptionType KExpr) (lget xs' p) (lget (ListType.cons KExpr x xs') (Nat.succ p)) (lget (ListType.cons KExpr y ys') (Nat.succ p)) (Eq.symm (OptionType KExpr) (lget (ListType.cons KExpr x xs') (Nat.succ p)) (lget xs' p) (lget_cons_succ x xs' p)) (hget (Nat.succ p) (Eq.substType Nat (fun (N : Nat) => Lt (Nat.succ p) N) (Nat.succ (list_length xs')) (list_length (ListType.cons KExpr x xs')) (Eq.symm Nat (list_length (ListType.cons KExpr x xs')) (Nat.succ (list_length xs')) (list_length_cons x xs')) (Lt.succ_lt_succ p (list_length xs') hp)))) (lget_cons_succ y ys' p))))) ys) xs",
            "list extensionality via lget: |xs|=|ys| and lget xs p = lget ys p for all in-range p => xs = ys. Double ListType.rec; absurd length cases bridged via list_length_nil/cons + nat_zero_ne_succ; cons/cons head via option_some_inj+lget_cons_zero, tail via ihx; Lt args substType-pinned via list_length_cons. SnSchema B4c (gateway to mapLT_instIter_fields).",
        )?;
        // Lt (inductive) -> nat_lt_b = true bridge (lget_ext/instIter_bvar_field use the
        // inductive Lt; the lookup tier — bvarSeq_lget, lget_at_ltb — uses the boolean
        // nat_lt_b whose succ/succ reduces by rfl). Lt.rec: zero_lt_succ -> refl (nat_lt_b 0
        // (succ n) is definitionally true); succ_lt_succ -> ih (nat_lt_b (succ)(succ) is
        // definitionally nat_lt_b).
        self.add_recursive_def(
            "def nat_lt_to_ltb (p : Nat) (q : Nat) (h : Lt p q) : Eq Bool (nat_lt_b p q) Bool.true := Lt.rec (fun (a : Nat) (b : Nat) (_ : Lt a b) => Eq Bool (nat_lt_b a b) Bool.true) (fun (n : Nat) => Eq.refl Bool Bool.true) (fun (n : Nat) (m : Nat) (h0 : Lt n m) (ih : Eq Bool (nat_lt_b n m) Bool.true) => ih) p q h",
            "Lt p q -> nat_lt_b p q = true (Lt.rec; both arms definitional via nat_lt_b succ/succ = nat_lt_b and 0/succ = true). SnSchema B4c bridge.",
        )?;
        self.add_recursive_def(
            "def bool_true_ne_false_prop (C : Prop) (h : Eq Bool Bool.true Bool.false) : C := Eq.substType Bool (fun (b : Bool) => Bool.rec (fun (_ : Bool) => Prop) C (Eq Bool Bool.true Bool.true) b) Bool.true Bool.false h (Eq.refl Bool Bool.true)",
            "Eq true false -> C for C:Prop (Bool.rec large-elim into Prop; true-branch (true=true) inhabited by refl, false-branch C). SnSchema B4c helper.",
        )?;
        // CPS-encoded existence (Exists.intro/rec are unregistered): `p < |xs|`
        // (as nat_lt_b=true, so the succ/succ and 0-bound reductions are
        // definitional) => there is an x with lget xs p = some x. ListType.rec on
        // xs; nil is impossible (nat_lt_b p 0 = false vs true, bool_true_ne_false_prop);
        // cons/0 hands over `a` via lget_cons_zero; cons/succ recurses (hb defeq at
        // succ index) and re-peels the witness through lget_cons_succ.
        self.add_recursive_def(
            "def lget_at_ltb (xs : ListType KExpr) : forall (p : Nat), Eq Bool (nat_lt_b p (list_length xs)) Bool.true -> forall (C : Prop), (forall (x : KExpr), Eq (OptionType KExpr) (lget xs p) (OptionType.some KExpr x) -> C) -> C := ListType.rec KExpr (fun (l : ListType KExpr) => forall (p : Nat), Eq Bool (nat_lt_b p (list_length l)) Bool.true -> forall (C : Prop), (forall (x : KExpr), Eq (OptionType KExpr) (lget l p) (OptionType.some KExpr x) -> C) -> C) (fun (p : Nat) (hb : Eq Bool (nat_lt_b p (list_length (ListType.nil KExpr))) Bool.true) (C : Prop) (k : forall (x : KExpr), Eq (OptionType KExpr) (lget (ListType.nil KExpr) p) (OptionType.some KExpr x) -> C) => bool_true_ne_false_prop C (Eq.trans Bool Bool.true (nat_lt_b p (list_length (ListType.nil KExpr))) Bool.false (Eq.symm Bool (nat_lt_b p (list_length (ListType.nil KExpr))) Bool.true hb) (Eq.trans Bool (nat_lt_b p (list_length (ListType.nil KExpr))) (nat_lt_b p Nat.zero) Bool.false (Eq.cong Nat Bool (fun (w : Nat) => nat_lt_b p w) (list_length (ListType.nil KExpr)) Nat.zero list_length_nil) (nat_lt_zero_false p)))) (fun (a : KExpr) (T : ListType KExpr) (ih : forall (p : Nat), Eq Bool (nat_lt_b p (list_length T)) Bool.true -> forall (C : Prop), (forall (x : KExpr), Eq (OptionType KExpr) (lget T p) (OptionType.some KExpr x) -> C) -> C) => fun (p : Nat) => Nat.rec (fun (pp : Nat) => Eq Bool (nat_lt_b pp (list_length (ListType.cons KExpr a T))) Bool.true -> forall (C : Prop), (forall (x : KExpr), Eq (OptionType KExpr) (lget (ListType.cons KExpr a T) pp) (OptionType.some KExpr x) -> C) -> C) (fun (hb : Eq Bool (nat_lt_b Nat.zero (list_length (ListType.cons KExpr a T))) Bool.true) (C : Prop) (k : forall (x : KExpr), Eq (OptionType KExpr) (lget (ListType.cons KExpr a T) Nat.zero) (OptionType.some KExpr x) -> C) => k a (lget_cons_zero a T)) (fun (p0 : Nat) (_ : Eq Bool (nat_lt_b p0 (list_length (ListType.cons KExpr a T))) Bool.true -> forall (C : Prop), (forall (x : KExpr), Eq (OptionType KExpr) (lget (ListType.cons KExpr a T) p0) (OptionType.some KExpr x) -> C) -> C) (hb : Eq Bool (nat_lt_b (Nat.succ p0) (list_length (ListType.cons KExpr a T))) Bool.true) (C : Prop) (k : forall (x : KExpr), Eq (OptionType KExpr) (lget (ListType.cons KExpr a T) (Nat.succ p0)) (OptionType.some KExpr x) -> C) => ih p0 hb C (fun (x : KExpr) (hx : Eq (OptionType KExpr) (lget T p0) (OptionType.some KExpr x)) => k x (Eq.trans (OptionType KExpr) (lget (ListType.cons KExpr a T) (Nat.succ p0)) (lget T p0) (OptionType.some KExpr x) (lget_cons_succ a T p0) hx))) p) xs",
            "p < |xs| (nat_lt_b=true) => exists x, lget xs p = some x (CPS-encoded; ListType.rec, nil absurd via nat_lt_zero_false+bool_true_ne_false_prop, cons/0 via lget_cons_zero, cons/succ recurse + lget_cons_succ). SnSchema B4c (lget_of_lt, Exists-free).",
        )?;
        // Witness-carried cons-append lookup: if `lget (m::ms) q = some cq` then
        // `lget (m::ms++fields) q = some cq`. NO bound / NO nat_lt_b needed — the
        // witness itself proves q is in range, and lget_append_lt carries the some
        // to the appended list (avoiding the nat_lt_b var/app drop-bug entirely).
        // Nat.rec on q: 0 -> both heads are `some m` (lget_cons_zero); succ q' ->
        // peel m both sides (lget_cons_succ), then lget_append_lt on the tail.
        self.add_recursive_def(
            "def lget_cons_append_some (m : KExpr) (ms : ListType KExpr) (fields : ListType KExpr) (cq : KExpr) : forall (q : Nat), Eq (OptionType KExpr) (lget (ListType.cons KExpr m ms) q) (OptionType.some KExpr cq) -> Eq (OptionType KExpr) (lget (ListType.cons KExpr m (list_append ms fields)) q) (OptionType.some KExpr cq) := Nat.rec (fun (q : Nat) => Eq (OptionType KExpr) (lget (ListType.cons KExpr m ms) q) (OptionType.some KExpr cq) -> Eq (OptionType KExpr) (lget (ListType.cons KExpr m (list_append ms fields)) q) (OptionType.some KExpr cq)) (fun (hcq : Eq (OptionType KExpr) (lget (ListType.cons KExpr m ms) Nat.zero) (OptionType.some KExpr cq)) => Eq.trans (OptionType KExpr) (lget (ListType.cons KExpr m (list_append ms fields)) Nat.zero) (lget (ListType.cons KExpr m ms) Nat.zero) (OptionType.some KExpr cq) (Eq.trans (OptionType KExpr) (lget (ListType.cons KExpr m (list_append ms fields)) Nat.zero) (OptionType.some KExpr m) (lget (ListType.cons KExpr m ms) Nat.zero) (lget_cons_zero m (list_append ms fields)) (Eq.symm (OptionType KExpr) (lget (ListType.cons KExpr m ms) Nat.zero) (OptionType.some KExpr m) (lget_cons_zero m ms))) hcq) (fun (q0 : Nat) (_ : Eq (OptionType KExpr) (lget (ListType.cons KExpr m ms) q0) (OptionType.some KExpr cq) -> Eq (OptionType KExpr) (lget (ListType.cons KExpr m (list_append ms fields)) q0) (OptionType.some KExpr cq)) (hcq : Eq (OptionType KExpr) (lget (ListType.cons KExpr m ms) (Nat.succ q0)) (OptionType.some KExpr cq)) => Eq.trans (OptionType KExpr) (lget (ListType.cons KExpr m (list_append ms fields)) (Nat.succ q0)) (lget (list_append ms fields) q0) (OptionType.some KExpr cq) (lget_cons_succ m (list_append ms fields) q0) (lget_append_lt fields ms q0 cq (Eq.trans (OptionType KExpr) (lget ms q0) (lget (ListType.cons KExpr m ms) (Nat.succ q0)) (OptionType.some KExpr cq) (Eq.symm (OptionType KExpr) (lget (ListType.cons KExpr m ms) (Nat.succ q0)) (lget ms q0) (lget_cons_succ m ms q0)) hcq)))",
            "lget (m::ms) q = some cq => lget (m::ms++fields) q = some cq (Nat.rec on q; 0 both some m, succ peel + lget_append_lt on tail). No bound/nat_lt_b. SnSchema B4c helper.",
        )?;
        // ── B4c crux (append_ge): `lget (xs ++ ys) (q + |xs|) = lget ys q`, the
        //    field-lookup-after-prefix fact. QUERY-FIRST (`q` is the first Nat.add
        //    operand), which makes BOTH recursor legs DEFINITIONAL:
        //      base:  `Nat.add q (list_length nil) ≡ Nat.add q Nat.zero ≡ q`
        //             (Nat.add recurses on its 2nd arg; nil→0→base iota) ⇒ refl;
        //      step:  `Nat.add q (list_length (cons a T)) ≡ Nat.add q (succ|T|)
        //             ≡ succ (Nat.add q |T|)`, then lget peels the literal succ
        //             onto the tail ⇒ exactly `ih q`.
        //    So there is NO nat_zero_add, NO OfNat/Const zero-bridging, NO
        //    applied-recursor unification — the recursor's own defeq check does it
        //    all. The index is written `(fun m => Nat.add q m) (list_length l)`
        //    (β≡ `Nat.add q (list_length l)`): the lambda-wrap is load-bearing —
        //    bare `Nat.add q (application)` hits a confirmed clean-elab bug that
        //    DROPS the 2nd operand ("expected Nat, got Nat -> Nat"; min repro
        //    `Nat.add q (Nat.succ q)`), and `(fun m => Nat.add q m) app` is the
        //    proven dodge (a plain application the elaborator handles). The
        //    LENGTH-first spelling elaborates but forces `0 + q = q`
        //    (nat_zero_add) whose library `0` is `OfNat.ofNat …` and collides with
        //    `Nat.zero`/`list_length nil` under the weak arg-unifier — a wall this
        //    query-first definitional form sidesteps entirely.
        self.add_recursive_def(
            "def lget_append_ge (ys : ListType KExpr) (xs : ListType KExpr) : forall (q : Nat), Eq (OptionType KExpr) (lget (list_append xs ys) ((fun (m : Nat) => Nat.add q m) (list_length xs))) (lget ys q) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (q : Nat), Eq (OptionType KExpr) (lget (list_append l ys) ((fun (m : Nat) => Nat.add q m) (list_length l))) (lget ys q)) (fun (q : Nat) => Eq.refl (OptionType KExpr) (lget ys q)) (fun (a : KExpr) (T : ListType KExpr) (ih : forall (q : Nat), Eq (OptionType KExpr) (lget (list_append T ys) ((fun (m : Nat) => Nat.add q m) (list_length T))) (lget ys q)) => fun (q : Nat) => ih q) xs",
            "lget (xs ++ ys) (q + list_length xs) = lget ys q. QUERY-FIRST lambda-wrapped index => base+step both definitional (refl / ih q), no nat_zero_add/OfNat/recursor-unification. SnSchema B4c crux (lget append_ge).",
        )?;
        self.add_recursive_def(
            "def lget_mapLT (f : KExpr -> KExpr) (xs : ListType KExpr) : forall (p : Nat) (x : KExpr), Eq (OptionType KExpr) (lget xs p) (OptionType.some KExpr x) -> Eq (OptionType KExpr) (lget (mapLT f xs) p) (OptionType.some KExpr (f x)) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (p : Nat) (x : KExpr), Eq (OptionType KExpr) (lget l p) (OptionType.some KExpr x) -> Eq (OptionType KExpr) (lget (mapLT f l) p) (OptionType.some KExpr (f x))) (fun (p : Nat) (x : KExpr) (h : Eq (OptionType KExpr) (lget (ListType.nil KExpr) p) (OptionType.some KExpr x)) => option_none_ne_some KExpr x (Eq (OptionType KExpr) (lget (mapLT f (ListType.nil KExpr)) p) (OptionType.some KExpr (f x))) h) (fun (a : KExpr) (T : ListType KExpr) (ih : forall (p : Nat) (x : KExpr), Eq (OptionType KExpr) (lget T p) (OptionType.some KExpr x) -> Eq (OptionType KExpr) (lget (mapLT f T) p) (OptionType.some KExpr (f x))) => fun (p : Nat) (x : KExpr) => Bool.rec (fun (b : Bool) => Eq (OptionType KExpr) (Bool.rec (fun (_ : Bool) => OptionType KExpr) (lget T (Nat.pred p)) (OptionType.some KExpr a) b) (OptionType.some KExpr x) -> Eq (OptionType KExpr) (Bool.rec (fun (_ : Bool) => OptionType KExpr) (lget (mapLT f T) (Nat.pred p)) (OptionType.some KExpr (f a)) b) (OptionType.some KExpr (f x))) (fun (hf : Eq (OptionType KExpr) (lget T (Nat.pred p)) (OptionType.some KExpr x)) => ih (Nat.pred p) x hf) (fun (ht : Eq (OptionType KExpr) (OptionType.some KExpr a) (OptionType.some KExpr x)) => Eq.cong KExpr (OptionType KExpr) (fun (z : KExpr) => OptionType.some KExpr (f z)) a x (option_some_inj KExpr a x ht)) (nat_is_zero p)) xs",
            "lget xs p = some x -> lget (mapLT f xs) p = some (f x). ListType.rec on xs; cons cases nat_is_zero p (true->cong some/f, false->ih). SnSchema B4c crux (lget).",
        )?;

        // ── B4c crux, bvarSeq descending-index lookup via lget. Structural Nat.rec
        // on n (bvarSeq shape) + inner Nat.rec on j (structural j=0/succ) — lget's
        // peels are clean (recurse on the concrete cons list, index via nat_is_zero,
        // no index-rewriting-over-lget). Base n=0 absurd (nat_lt_zero_false +
        // bool_false_ne_true); j=0 head is refl; j=succ bridges peel + outer IH at
        // top-1 + nat_sub_pred_comm ((top-1)-j = top-(succ j)).
        self.add_recursive_def(
            "def bvarSeq_lget_peel (top : Nat) (n0 : Nat) (j0 : Nat) : Eq (OptionType KExpr) (lget (bvarSeq top (Nat.succ n0)) (Nat.succ j0)) (lget (bvarSeq (Nat.sub top (Nat.succ Nat.zero)) n0) j0) := Eq.refl (OptionType KExpr) (lget (bvarSeq (Nat.sub top (Nat.succ Nat.zero)) n0) j0)",
            "lget (bvarSeq top (succ n0)) (succ j0) = lget (bvarSeq (top-1) n0) j0 (standalone refl; bvarSeq fires to cons, lget peels succ index). SnSchema B4c crux (lget).",
        )?;
        self.add_recursive_def(
            "def bvarSeq_lget (n : Nat) : forall (top : Nat) (j : Nat), Eq Bool (nat_lt_b j n) Bool.true -> Eq (OptionType KExpr) (lget (bvarSeq top n) j) (OptionType.some KExpr (KExpr.bvar (Nat.sub top j))) := Nat.rec (fun (k : Nat) => forall (top : Nat) (j : Nat), Eq Bool (nat_lt_b j k) Bool.true -> Eq (OptionType KExpr) (lget (bvarSeq top k) j) (OptionType.some KExpr (KExpr.bvar (Nat.sub top j)))) (fun (top : Nat) (j : Nat) (h : Eq Bool (nat_lt_b j Nat.zero) Bool.true) => bool_false_ne_true (Eq (OptionType KExpr) (lget (bvarSeq top Nat.zero) j) (OptionType.some KExpr (KExpr.bvar (Nat.sub top j)))) (Eq.trans Bool Bool.false (nat_lt_b j Nat.zero) Bool.true (Eq.symm Bool (nat_lt_b j Nat.zero) Bool.false (nat_lt_zero_false j)) h)) (fun (n0 : Nat) (ih : forall (top : Nat) (j : Nat), Eq Bool (nat_lt_b j n0) Bool.true -> Eq (OptionType KExpr) (lget (bvarSeq top n0) j) (OptionType.some KExpr (KExpr.bvar (Nat.sub top j)))) => fun (top : Nat) => fun (j : Nat) => Nat.rec (fun (jj : Nat) => Eq Bool (nat_lt_b jj (Nat.succ n0)) Bool.true -> Eq (OptionType KExpr) (lget (bvarSeq top (Nat.succ n0)) jj) (OptionType.some KExpr (KExpr.bvar (Nat.sub top jj)))) (fun (h : Eq Bool (nat_lt_b Nat.zero (Nat.succ n0)) Bool.true) => Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.bvar top))) (fun (j0 : Nat) (_ : Eq Bool (nat_lt_b j0 (Nat.succ n0)) Bool.true -> Eq (OptionType KExpr) (lget (bvarSeq top (Nat.succ n0)) j0) (OptionType.some KExpr (KExpr.bvar (Nat.sub top j0)))) (h : Eq Bool (nat_lt_b (Nat.succ j0) (Nat.succ n0)) Bool.true) => Eq.trans (OptionType KExpr) (lget (bvarSeq top (Nat.succ n0)) (Nat.succ j0)) (lget (bvarSeq (Nat.sub top (Nat.succ Nat.zero)) n0) j0) (OptionType.some KExpr (KExpr.bvar (Nat.pred (Nat.sub top j0)))) (bvarSeq_lget_peel top n0 j0) (Eq.trans (OptionType KExpr) (lget (bvarSeq (Nat.sub top (Nat.succ Nat.zero)) n0) j0) (OptionType.some KExpr (KExpr.bvar (Nat.sub (Nat.pred top) j0))) (OptionType.some KExpr (KExpr.bvar (Nat.pred (Nat.sub top j0)))) (ih (Nat.sub top (Nat.succ Nat.zero)) j0 (Eq.trans Bool (nat_lt_b j0 n0) (nat_lt_b (Nat.succ j0) (Nat.succ n0)) Bool.true (Eq.symm Bool (nat_lt_b (Nat.succ j0) (Nat.succ n0)) (nat_lt_b j0 n0) (nat_lt_b_succ_succ j0 n0)) h)) (Eq.cong Nat (OptionType KExpr) (fun (z : Nat) => OptionType.some KExpr (KExpr.bvar z)) (Nat.sub (Nat.pred top) j0) (Nat.pred (Nat.sub top j0)) (nat_sub_pred_comm top j0)))) j) n",
            "nat_lt_b j n = true -> lget (bvarSeq top n) j = some (bvar (top - j)) (Nat.rec on n, structural Nat.rec on j; lget peels + nat_sub_pred_comm). SnSchema B4c crux (lget).",
        )?;

        // ── B4c crux, LIFT machinery for instIter_bvar: instIter eats the residual
        // lifts. inst_at_lift_succ specializes the (Aristotle-proven) general
        // instantiate-after-lift cancellation; instIter_lift_cancel iterates it.
        self.add_recursive_def(
            "def inst_at_lift_succ (a : KExpr) (b : KExpr) (n : Nat) : Eq KExpr (instantiate_at (lift_at a Nat.zero (Nat.succ n)) b n) (lift_at a Nat.zero n) := Eq.trans KExpr (instantiate_at (lift_at a Nat.zero (Nat.succ n)) b n) (instantiate_at (lift_at a Nat.zero (Nat.succ n)) b (Nat.add Nat.zero n)) (lift_at a Nat.zero n) (Eq.cong Nat KExpr (fun (D : Nat) => instantiate_at (lift_at a Nat.zero (Nat.succ n)) b D) n (Nat.add Nat.zero n) (Eq.symm Nat (Nat.add Nat.zero n) n (nat_zero_add n))) (instantiate_lift_cancel_general a b Nat.zero (Nat.succ n) n (Eq.substType Nat (fun (S : Nat) => Eq Nat S (Nat.succ (Nat.sub S (Nat.succ Nat.zero)))) (Nat.succ Nat.zero) (Nat.sub (Nat.succ n) n) (Eq.symm Nat (Nat.sub (Nat.succ n) n) (Nat.succ Nat.zero) (nat_sub_succ_self n)) (Eq.refl Nat (Nat.succ Nat.zero))))",
            "instantiate_at (lift_at a 0 (succ n)) b n = lift_at a 0 n (specialize instantiate_lift_cancel_general c=0,a=succ n,j=n; guard via nat_sub_succ_self; depth bridge via nat_zero_add). SnSchema B4c crux.",
        )?;
        self.add_recursive_def(
            "def instIter_lift_cancel (a : KExpr) (rest : ListType KExpr) : Eq KExpr (instIter (lift_at a Nat.zero (list_length rest)) rest) a := ListType.rec KExpr (fun (l : ListType KExpr) => Eq KExpr (instIter (lift_at a Nat.zero (list_length l)) l) a) (lift_at_amount_zero a Nat.zero) (fun (b : KExpr) (rest2 : ListType KExpr) (ih : Eq KExpr (instIter (lift_at a Nat.zero (list_length rest2)) rest2) a) => Eq.substType KExpr (fun (E : KExpr) => Eq KExpr (instIter E rest2) a) (lift_at a Nat.zero (list_length rest2)) (instantiate_at (lift_at a Nat.zero (Nat.succ (list_length rest2))) b (list_length rest2)) (Eq.symm KExpr (instantiate_at (lift_at a Nat.zero (Nat.succ (list_length rest2))) b (list_length rest2)) (lift_at a Nat.zero (list_length rest2)) (inst_at_lift_succ a b (list_length rest2))) ih) rest",
            "instIter (lift_at a 0 |rest|) rest = a (ListType.rec on rest; base lift_at_amount_zero, step eats one lift via inst_at_lift_succ). SnSchema B4c crux.",
        )?;
        // Bridge boolean nat_lt_b to the inductive Lt (Type-valued), so the guard
        // lemma lt_sub_succ (Lt i c -> Nat.sub c i = succ((c-i)-1)) is available for
        // instIter_bvar's instantiate_bvar_at_below application.
        self.add_recursive_def(
            "def nat_ltb_to_lt (i : Nat) : forall (c : Nat), Eq Bool (nat_lt_b i c) Bool.true -> Lt i c := Nat.rec (fun (ii : Nat) => forall (c : Nat), Eq Bool (nat_lt_b ii c) Bool.true -> Lt ii c) (fun (c : Nat) => Nat.rec (fun (cc : Nat) => Eq Bool (nat_lt_b Nat.zero cc) Bool.true -> Lt Nat.zero cc) (fun (h : Eq Bool (nat_lt_b Nat.zero Nat.zero) Bool.true) => bool_true_ne_false (Lt Nat.zero Nat.zero) (Eq.symm Bool (nat_lt_b Nat.zero Nat.zero) Bool.true h)) (fun (c0 : Nat) (_ : Eq Bool (nat_lt_b Nat.zero c0) Bool.true -> Lt Nat.zero c0) (h : Eq Bool (nat_lt_b Nat.zero (Nat.succ c0)) Bool.true) => Lt.zero_lt_succ c0) c) (fun (i0 : Nat) (ih : forall (c : Nat), Eq Bool (nat_lt_b i0 c) Bool.true -> Lt i0 c) => fun (c : Nat) => Nat.rec (fun (cc : Nat) => Eq Bool (nat_lt_b (Nat.succ i0) cc) Bool.true -> Lt (Nat.succ i0) cc) (fun (h : Eq Bool (nat_lt_b (Nat.succ i0) Nat.zero) Bool.true) => bool_true_ne_false (Lt (Nat.succ i0) Nat.zero) (Eq.symm Bool (nat_lt_b (Nat.succ i0) Nat.zero) Bool.true h)) (fun (c0 : Nat) (_ : Eq Bool (nat_lt_b (Nat.succ i0) c0) Bool.true -> Lt (Nat.succ i0) c0) (h : Eq Bool (nat_lt_b (Nat.succ i0) (Nat.succ c0)) Bool.true) => Lt.succ_lt_succ i0 c0 (ih c0 h)) c) i",
            "nat_lt_b i c = true -> Lt i c (Nat.rec on i, inner Nat.rec on c; c=0 absurd via bool_true_ne_false [Type-CPS, Lt is Type], succ/succ peels to ih via Lt.succ_lt_succ, zero/succ = Lt.zero_lt_succ). SnSchema B4c crux.",
        )?;
        self.add_recursive_def(
            "def nat_ltb_succ_not_lt_eq (i : Nat) : forall (d : Nat), Eq Bool (nat_lt_b i (Nat.succ d)) Bool.true -> Eq Bool (nat_lt_b i d) Bool.false -> Eq Nat i d := Nat.rec (fun (ii : Nat) => forall (d : Nat), Eq Bool (nat_lt_b ii (Nat.succ d)) Bool.true -> Eq Bool (nat_lt_b ii d) Bool.false -> Eq Nat ii d) (fun (d : Nat) => Nat.rec (fun (dd : Nat) => Eq Bool (nat_lt_b Nat.zero (Nat.succ dd)) Bool.true -> Eq Bool (nat_lt_b Nat.zero dd) Bool.false -> Eq Nat Nat.zero dd) (fun (h1 : Eq Bool (nat_lt_b Nat.zero (Nat.succ Nat.zero)) Bool.true) (h2 : Eq Bool (nat_lt_b Nat.zero Nat.zero) Bool.false) => Eq.refl Nat Nat.zero) (fun (d0 : Nat) (_ : Eq Bool (nat_lt_b Nat.zero (Nat.succ d0)) Bool.true -> Eq Bool (nat_lt_b Nat.zero d0) Bool.false -> Eq Nat Nat.zero d0) (h1 : Eq Bool (nat_lt_b Nat.zero (Nat.succ (Nat.succ d0))) Bool.true) (h2 : Eq Bool (nat_lt_b Nat.zero (Nat.succ d0)) Bool.false) => bool_false_ne_true (Eq Nat Nat.zero (Nat.succ d0)) (Eq.symm Bool (nat_lt_b Nat.zero (Nat.succ d0)) Bool.false h2)) d) (fun (i0 : Nat) (ih : forall (d : Nat), Eq Bool (nat_lt_b i0 (Nat.succ d)) Bool.true -> Eq Bool (nat_lt_b i0 d) Bool.false -> Eq Nat i0 d) => fun (d : Nat) => Nat.rec (fun (dd : Nat) => Eq Bool (nat_lt_b (Nat.succ i0) (Nat.succ dd)) Bool.true -> Eq Bool (nat_lt_b (Nat.succ i0) dd) Bool.false -> Eq Nat (Nat.succ i0) dd) (fun (h1 : Eq Bool (nat_lt_b (Nat.succ i0) (Nat.succ Nat.zero)) Bool.true) (h2 : Eq Bool (nat_lt_b (Nat.succ i0) Nat.zero) Bool.false) => bool_false_ne_true (Eq Nat (Nat.succ i0) Nat.zero) (Eq.trans Bool Bool.false (nat_lt_b (Nat.succ i0) (Nat.succ Nat.zero)) Bool.true (Eq.symm Bool (nat_lt_b (Nat.succ i0) (Nat.succ Nat.zero)) Bool.false (nat_lt_zero_false i0)) h1)) (fun (d0 : Nat) (_ : Eq Bool (nat_lt_b (Nat.succ i0) (Nat.succ d0)) Bool.true -> Eq Bool (nat_lt_b (Nat.succ i0) d0) Bool.false -> Eq Nat (Nat.succ i0) d0) (h1 : Eq Bool (nat_lt_b (Nat.succ i0) (Nat.succ (Nat.succ d0))) Bool.true) (h2 : Eq Bool (nat_lt_b (Nat.succ i0) (Nat.succ d0)) Bool.false) => Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) i0 d0 (ih d0 h1 h2)) d) i",
            "nat_lt_b i (succ d) = true -> nat_lt_b i d = false -> i = d (i<=d and i>=d => i=d; Nat.rec on i, inner on d; nat_lt_b peels defeq, absurd branches via bool_false_ne_true, succ/succ via Eq.cong+ih). SnSchema B4c crux.",
        )?;
        self.add_recursive_def(
            "def nat_ltb_lt_succ_add (i : Nat) : forall (k : Nat), Eq Bool (nat_lt_b i (Nat.succ (Nat.add i k))) Bool.true := Nat.rec (fun (ii : Nat) => forall (k : Nat), Eq Bool (nat_lt_b ii (Nat.succ (Nat.add ii k))) Bool.true) (fun (k : Nat) => Eq.refl Bool Bool.true) (fun (i0 : Nat) (ih : forall (k : Nat), Eq Bool (nat_lt_b i0 (Nat.succ (Nat.add i0 k))) Bool.true) => fun (k : Nat) => Eq.substType Nat (fun (N : Nat) => Eq Bool (nat_lt_b i0 N) Bool.true) (Nat.succ (Nat.add i0 k)) (Nat.add (Nat.succ i0) k) (Eq.symm Nat (Nat.add (Nat.succ i0) k) (Nat.succ (Nat.add i0 k)) (nat_succ_add i0 k)) (ih k)) i",
            "nat_lt_b i (succ (i + k)) = true (i < succ(i+k) always). Nat.rec on i; base nat_lt_b 0 (succ _)=true rfl; step peels succ/succ, substType over the STUCK nat_lt_b i0 N (i0 var) to reshape Nat.add (succ i0) k = succ(Nat.add i0 k). SnSchema B4c crux.",
        )?;
        // ── B4c crux, THE LINCHPIN: instIter_bvar (additive index). Resolves
        // instIter (bvar i) args to the k-th element when succ i + k = |args|.
        self.add_recursive_def(
            "def instIter_bvar (args : ListType KExpr) : forall (i : Nat) (k : Nat) (v : KExpr), Eq Nat (Nat.add (Nat.succ i) k) (list_length args) -> Eq (OptionType KExpr) (lget args k) (OptionType.some KExpr v) -> Eq KExpr (instIter (KExpr.bvar i) args) v := ListType.rec KExpr (fun (l : ListType KExpr) => forall (i : Nat) (k : Nat) (v : KExpr), Eq Nat (Nat.add (Nat.succ i) k) (list_length l) -> Eq (OptionType KExpr) (lget l k) (OptionType.some KExpr v) -> Eq KExpr (instIter (KExpr.bvar i) l) v) (fun (i : Nat) (k : Nat) (v : KExpr) (heq : Eq Nat (Nat.add (Nat.succ i) k) (list_length (ListType.nil KExpr))) (hget : Eq (OptionType KExpr) (lget (ListType.nil KExpr) k) (OptionType.some KExpr v)) => option_none_ne_some KExpr v (Eq KExpr (instIter (KExpr.bvar i) (ListType.nil KExpr)) v) hget) (fun (a : KExpr) (rest : ListType KExpr) (ih : forall (i : Nat) (k : Nat) (v : KExpr), Eq Nat (Nat.add (Nat.succ i) k) (list_length rest) -> Eq (OptionType KExpr) (lget rest k) (OptionType.some KExpr v) -> Eq KExpr (instIter (KExpr.bvar i) rest) v) => fun (i : Nat) (k : Nat) (v : KExpr) => Nat.rec (fun (kk : Nat) => Eq Nat (Nat.add (Nat.succ i) kk) (list_length (ListType.cons KExpr a rest)) -> Eq (OptionType KExpr) (lget (ListType.cons KExpr a rest) kk) (OptionType.some KExpr v) -> Eq KExpr (instIter (KExpr.bvar i) (ListType.cons KExpr a rest)) v) (fun (heq0 : Eq Nat (Nat.add (Nat.succ i) Nat.zero) (list_length (ListType.cons KExpr a rest))) (hget0 : Eq (OptionType KExpr) (lget (ListType.cons KExpr a rest) Nat.zero) (OptionType.some KExpr v)) => Eq.trans KExpr (instIter (KExpr.bvar i) (ListType.cons KExpr a rest)) (instIter (lift_at a Nat.zero (list_length rest)) rest) v (Eq.cong KExpr KExpr (fun (E : KExpr) => instIter E rest) (instantiate_at (KExpr.bvar i) a (list_length rest)) (lift_at a Nat.zero (list_length rest)) (Eq.trans KExpr (instantiate_at (KExpr.bvar i) a (list_length rest)) (instantiate_bvar_at i (list_length rest) a) (lift_at a Nat.zero (list_length rest)) (instantiate_at_bvar i a (list_length rest)) (Eq.substType Nat (fun (N : Nat) => Eq KExpr (instantiate_bvar_at N (list_length rest) a) (lift_at a Nat.zero (list_length rest))) (list_length rest) i (Eq.symm Nat i (list_length rest) (nat_succ_inj i (list_length rest) heq0)) (instantiate_bvar_at_eq (list_length rest) a)))) (Eq.trans KExpr (instIter (lift_at a Nat.zero (list_length rest)) rest) a v (instIter_lift_cancel a rest) (option_some_inj KExpr a v hget0))) (fun (k0 : Nat) (_ : Eq Nat (Nat.add (Nat.succ i) k0) (list_length (ListType.cons KExpr a rest)) -> Eq (OptionType KExpr) (lget (ListType.cons KExpr a rest) k0) (OptionType.some KExpr v) -> Eq KExpr (instIter (KExpr.bvar i) (ListType.cons KExpr a rest)) v) (heqs : Eq Nat (Nat.add (Nat.succ i) (Nat.succ k0)) (list_length (ListType.cons KExpr a rest))) (hgets : Eq (OptionType KExpr) (lget (ListType.cons KExpr a rest) (Nat.succ k0)) (OptionType.some KExpr v)) => Eq.trans KExpr (instIter (KExpr.bvar i) (ListType.cons KExpr a rest)) (instIter (KExpr.bvar i) rest) v (Eq.cong KExpr KExpr (fun (E : KExpr) => instIter E rest) (instantiate_at (KExpr.bvar i) a (list_length rest)) (KExpr.bvar i) (Eq.trans KExpr (instantiate_at (KExpr.bvar i) a (list_length rest)) (instantiate_bvar_at i (list_length rest) a) (KExpr.bvar i) (instantiate_at_bvar i a (list_length rest)) (instantiate_bvar_at_below i (list_length rest) a (lt_sub_succ i (list_length rest) (nat_ltb_to_lt i (list_length rest) (Eq.substType Nat (fun (N : Nat) => Eq Bool (nat_lt_b i N) Bool.true) (Nat.succ (Nat.add i k0)) (list_length rest) (Eq.trans Nat (Nat.succ (Nat.add i k0)) (Nat.add (Nat.succ i) k0) (list_length rest) (Eq.symm Nat (Nat.add (Nat.succ i) k0) (Nat.succ (Nat.add i k0)) (nat_succ_add i k0)) (nat_succ_inj (Nat.add (Nat.succ i) k0) (list_length rest) heqs)) (nat_ltb_lt_succ_add i k0))))))) (ih i k0 v (nat_succ_inj (Nat.add (Nat.succ i) k0) (list_length rest) heqs) (Eq.trans (OptionType KExpr) (lget rest k0) (lget (ListType.cons KExpr a rest) (Nat.succ k0)) (OptionType.some KExpr v) (Eq.symm (OptionType KExpr) (lget (ListType.cons KExpr a rest) (Nat.succ k0)) (lget rest k0) (lget_cons_succ a rest k0)) hgets))) k) args",
            "instIter (bvar i) args = v when succ i + k = |args| and lget args k = some v. ADDITIVE index (dodges lget index-rewrite). ListType.rec on args; nil absurd (lget nil k = none); cons Nat.rec on k: k=0 => i=|rest| (nat_succ_inj), instantiate = lift (instantiate_bvar_at_eq), instIter_lift_cancel; k=succ => lget peels (lget_cons_succ), instantiate = bvar i (instantiate_bvar_at_below + lt_sub_succ o nat_ltb_to_lt o nat_ltb_lt_succ_add), IH. THE LINCHPIN. SnSchema B4c crux.",
        )?;
        // Additive-index arithmetic for instIter_bvar_field: succ(r-1-p) + succ(p+mslen) = succ(mslen+r) when p<r.
        self.add_recursive_def(
            "def field_index_eq (r : Nat) (p : Nat) (mslen : Nat) (hlt : Lt p r) : Eq Nat (Nat.add (Nat.succ (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (Nat.succ (Nat.add p mslen))) (Nat.succ (Nat.add mslen r)) := Eq.trans Nat (Nat.add (Nat.succ (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (Nat.succ (Nat.add p mslen))) (Nat.succ (Nat.add (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p) (Nat.succ (Nat.add p mslen)))) (Nat.succ (Nat.add mslen r)) (nat_succ_add (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p) (Nat.succ (Nat.add p mslen))) (Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (Nat.add (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p) (Nat.succ (Nat.add p mslen))) (Nat.add mslen r) (Eq.trans Nat (Nat.add (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p) (Nat.succ (Nat.add p mslen))) (Nat.succ (Nat.add (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p) (Nat.add p mslen))) (Nat.add mslen r) (nat_add_succ_right (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p) (Nat.add p mslen)) (Eq.trans Nat (Nat.succ (Nat.add (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p) (Nat.add p mslen))) (Nat.succ (Nat.add (Nat.sub r (Nat.succ Nat.zero)) mslen)) (Nat.add mslen r) (Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (Nat.add (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p) (Nat.add p mslen)) (Nat.add (Nat.sub r (Nat.succ Nat.zero)) mslen) (Eq.trans Nat (Nat.add (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p) (Nat.add p mslen)) (Nat.add (Nat.add (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p) p) mslen) (Nat.add (Nat.sub r (Nat.succ Nat.zero)) mslen) (Eq.symm Nat (Nat.add (Nat.add (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p) p) mslen) (Nat.add (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p) (Nat.add p mslen)) (nat_add_assoc (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p) p mslen)) (Eq.cong Nat Nat (fun (w : Nat) => Nat.add w mslen) (Nat.add (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p) p) (Nat.sub r (Nat.succ Nat.zero)) (nat_sub_add_cancel p (Nat.sub r (Nat.succ Nat.zero)) (lt_succ_to_le p (Nat.sub r (Nat.succ Nat.zero)) (Eq.substType Nat (fun (N : Nat) => Lt p N) r (Nat.succ (Nat.sub r (Nat.succ Nat.zero))) (Eq.symm Nat (Nat.succ (Nat.sub r (Nat.succ Nat.zero))) r (nat_succ_sub1_of_lt p r hlt)) hlt)))))) (Eq.trans Nat (Nat.succ (Nat.add (Nat.sub r (Nat.succ Nat.zero)) mslen)) (Nat.add r mslen) (Nat.add mslen r) (Eq.trans Nat (Nat.succ (Nat.add (Nat.sub r (Nat.succ Nat.zero)) mslen)) (Nat.add (Nat.succ (Nat.sub r (Nat.succ Nat.zero))) mslen) (Nat.add r mslen) (Eq.symm Nat (Nat.add (Nat.succ (Nat.sub r (Nat.succ Nat.zero))) mslen) (Nat.succ (Nat.add (Nat.sub r (Nat.succ Nat.zero)) mslen)) (nat_succ_add (Nat.sub r (Nat.succ Nat.zero)) mslen)) (Eq.cong Nat Nat (fun (w : Nat) => Nat.add w mslen) (Nat.succ (Nat.sub r (Nat.succ Nat.zero))) r (nat_succ_sub1_of_lt p r hlt))) (nat_add_comm r mslen)))))",
            "succ(r-1-p) + succ(p+mslen) = succ(mslen+r) when Lt p r. Chain: nat_add_succ_right/nat_add_assoc/nat_sub_add_cancel [Le p (r-1) via lt_succ_to_le o substType(nat_succ_sub1_of_lt)]/nat_succ_add/nat_add_comm. The additive index eq feeding instIter_bvar for instIter_bvar_field. SnSchema B4c crux.",
        )?;
        // ── B4c: instIter_bvar_field — `instIter` resolves the (r-1-p)-th
        //    descending bvar (over the recursive-call prefix `m :: ms ++ fields`)
        //    to the p-th field `fp`. Applies the linchpin instIter_bvar with
        //    i = r-1-p, k = succ(p + |ms|):
        //      • index leg: field_index_eq gives `succ i + k = succ(|ms|+r)`,
        //        bridged to `|cons m (ms++fields)|` via list_append_length + hfl;
        //      • lookup leg: `lget (cons m (ms++fields)) k` peels m via
        //        lget_cons_succ to `lget (ms++fields) (p+|ms|)`, then lget_append_ge
        //        (query-first, β-matched) rewrites to `lget fields p`, = hfp.
        //    Mirrors guide instIter_bvar_field (SnSchema.lean).
        self.add_recursive_def(
            "def instIter_bvar_field (m : KExpr) (ms : ListType KExpr) (fields : ListType KExpr) (r : Nat) (p : Nat) (fp : KExpr) (hfl : Eq Nat (list_length fields) r) (hp : Lt p r) (hfp : Eq (OptionType KExpr) (lget fields p) (OptionType.some KExpr fp)) : Eq KExpr (instIter (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.cons KExpr m (list_append ms fields))) fp := instIter_bvar (ListType.cons KExpr m (list_append ms fields)) (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p) (Nat.succ (Nat.add p (list_length ms))) fp (Eq.trans Nat (Nat.add (Nat.succ (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (Nat.succ (Nat.add p (list_length ms)))) (Nat.succ (Nat.add (list_length ms) r)) (list_length (ListType.cons KExpr m (list_append ms fields))) (field_index_eq r p (list_length ms) hp) (Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (Nat.add (list_length ms) r) (list_length (list_append ms fields)) (Eq.symm Nat (list_length (list_append ms fields)) (Nat.add (list_length ms) r) (Eq.trans Nat (list_length (list_append ms fields)) (Nat.add (list_length ms) (list_length fields)) (Nat.add (list_length ms) r) (list_append_length ms fields) (Eq.cong Nat Nat (fun (w : Nat) => Nat.add (list_length ms) w) (list_length fields) r hfl))))) (Eq.trans (OptionType KExpr) (lget (ListType.cons KExpr m (list_append ms fields)) (Nat.succ (Nat.add p (list_length ms)))) (lget (list_append ms fields) (Nat.add p (list_length ms))) (OptionType.some KExpr fp) (lget_cons_succ m (list_append ms fields) (Nat.add p (list_length ms))) (Eq.trans (OptionType KExpr) (lget (list_append ms fields) (Nat.add p (list_length ms))) (lget fields p) (OptionType.some KExpr fp) (lget_append_ge fields ms p) hfp))",
            "instIter (bvar (r-1-p)) (cons m (ms ++ fields)) = fp when |fields|=r, p<r, lget fields p = some fp. Applies instIter_bvar with k=succ(p+|ms|); index via field_index_eq + list_append_length bridge, lookup via lget_cons_succ peel + lget_append_ge. SnSchema B4c.",
        )?;
        // ── B4c: mapLT_instIter_fields — the field-prefix of the rhs body resolves
        //    back to `fields`. `mapLT (fun t => instIter t (m :: ms ++ fields))
        //    (bvarSeq (r-1) r) = fields`, proven by lget_ext: equal length (mapLT_length
        //    + bvarSeq_length + hfl); and at each in-range p, the mapped bvarSeq entry
        //    `instIter (bvar (r-1-p)) (m :: ms ++ fields)` equals `fields[p]` — lget_mapLT
        //    over bvarSeq_lget lands `some (instIter (bvar (r-1-p)) ..)`, instIter_bvar_field
        //    equates it to fp, and lget_at_ltb (Lt->nat_lt_b via nat_lt_to_ltb) supplies fp.
        //    Guide mapLT_instIter_fields (SnSchema.lean L5777).
        self.add_recursive_def(
            "def mapLT_instIter_fields (m : KExpr) (ms : ListType KExpr) (fields : ListType KExpr) (r : Nat) (hfl : Eq Nat (list_length fields) r) : Eq (ListType KExpr) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) fields := lget_ext (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) fields (Eq.trans Nat (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) r (list_length fields) (Eq.trans Nat (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) (list_length (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) r (mapLT_length (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) (bvarSeq_length r (Nat.sub r (Nat.succ Nat.zero)))) (Eq.symm Nat (list_length fields) r hfl)) (fun (p : Nat) (hp : Lt p (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) => lget_at_ltb fields p (Eq.trans Bool (nat_lt_b p (list_length fields)) (nat_lt_b p r) Bool.true (Eq.cong Nat Bool (fun (w : Nat) => nat_lt_b p w) (list_length fields) r hfl) (nat_lt_to_ltb p r (Eq.substType Nat (fun (N : Nat) => Lt p N) (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) r (Eq.trans Nat (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) (list_length (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) r (mapLT_length (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) (bvarSeq_length r (Nat.sub r (Nat.succ Nat.zero)))) hp))) (Eq (OptionType KExpr) (lget (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) p) (lget fields p)) (fun (fp : KExpr) (hfp : Eq (OptionType KExpr) (lget fields p) (OptionType.some KExpr fp)) => Eq.trans (OptionType KExpr) (lget (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) p) (OptionType.some KExpr fp) (lget fields p) (Eq.trans (OptionType KExpr) (lget (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) p) (OptionType.some KExpr (instIter (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.cons KExpr m (list_append ms fields)))) (OptionType.some KExpr fp) (lget_mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) p (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (bvarSeq_lget r (Nat.sub r (Nat.succ Nat.zero)) p (nat_lt_to_ltb p r (Eq.substType Nat (fun (N : Nat) => Lt p N) (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) r (Eq.trans Nat (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) (list_length (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) r (mapLT_length (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) (bvarSeq_length r (Nat.sub r (Nat.succ Nat.zero)))) hp)))) (Eq.cong KExpr (OptionType KExpr) (fun (w : KExpr) => OptionType.some KExpr w) (instIter (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.cons KExpr m (list_append ms fields))) fp (instIter_bvar_field m ms fields r p fp hfl (Eq.substType Nat (fun (N : Nat) => Lt p N) (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) r (Eq.trans Nat (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) (list_length (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) r (mapLT_length (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) (bvarSeq_length r (Nat.sub r (Nat.succ Nat.zero)))) hp) hfp))) (Eq.symm (OptionType KExpr) (lget fields p) (OptionType.some KExpr fp) hfp)))",
            "mapLT (fun t => instIter t (m :: ms ++ fields)) (bvarSeq (r-1) r) = fields when |fields|=r. Via lget_ext: length (mapLT_length+bvarSeq_length+hfl); per-index instIter (bvar (r-1-p)) .. = fields[p] via lget_mapLT o bvarSeq_lget + instIter_bvar_field, witness from lget_at_ltb. SnSchema B4c.",
        )?;
        // Prefix index arithmetic for instIter_bvar in mapLT_instIter_prefix:
        // succ((r+k)-q) + q = succ(k+r) when q <= r+k. The sum r+k is THREADED as a
        // bare variable `rk` (`hrk : r+k = rk`) so every `Le`/`Nat.sub`/`Nat.add`
        // here has bare-var operands — dodges the `<2-arg head> <def-param> <app>`
        // clean-elab drop-bug (which otherwise bites `Le q (Nat.add r k)`). Caller
        // passes rk := Nat.add r k (both its own vars, no drop) + refl.
        self.add_recursive_def(
            "def prefix_index_eq (r : Nat) (k : Nat) (q : Nat) (rk : Nat) (hrk : Eq Nat (Nat.add r k) rk) (hqrk : Le q rk) : Eq Nat (Nat.add (Nat.succ (Nat.sub rk q)) q) (Nat.succ (Nat.add k r)) := Eq.trans Nat (Nat.add (Nat.succ (Nat.sub rk q)) q) (Nat.succ (Nat.add (Nat.sub rk q) q)) (Nat.succ (Nat.add k r)) (nat_succ_add (Nat.sub rk q) q) (Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (Nat.add (Nat.sub rk q) q) (Nat.add k r) (Eq.trans Nat (Nat.add (Nat.sub rk q) q) rk (Nat.add k r) (nat_sub_add_cancel q rk hqrk) (Eq.trans Nat rk (Nat.add r k) (Nat.add k r) (Eq.symm Nat (Nat.add r k) rk hrk) (nat_add_comm r k))))",
            "succ(rk-q) + q = succ(k+r) when Le q rk and r+k=rk (rk threaded as bare var to dodge the Le/Nat.add def-param drop-bug). nat_succ_add + nat_sub_add_cancel + nat_add_comm. Feeds instIter_bvar for mapLT_instIter_prefix. SnSchema B4c.",
        )?;
        // ── B4c: mapLT_instIter_prefix — the recursive-call prefix `[C,m_0..m_(k-1)]`
        //    resolves back to `m :: ms`. Four small length/order helpers factor the
        //    big term (parser Qq drop-bug now fixed, so `Lt q (…)`/`nat_lt_b q (…)`
        //    are clean). Guide mapLT_instIter_prefix (SnSchema.lean L5791).
        self.add_recursive_def(
            "def prefix_len_eq (m : KExpr) (ms : ListType KExpr) (fields : ListType KExpr) (r : Nat) (k : Nat) : Eq Nat (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r k) (Nat.succ k)))) (Nat.succ k) := Eq.trans Nat (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r k) (Nat.succ k)))) (list_length (bvarSeq (Nat.add r k) (Nat.succ k))) (Nat.succ k) (mapLT_length (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r k) (Nat.succ k))) (bvarSeq_length (Nat.succ k) (Nat.add r k))",
            "|mapLT F (bvarSeq (r+k)(k+1))| = k+1 (mapLT_length + bvarSeq_length). SnSchema B4c (mapLT_instIter_prefix helper).",
        )?;
        self.add_recursive_def(
            "def prefix_len_eq2 (m : KExpr) (ms : ListType KExpr) (k : Nat) (hk : Eq Nat (list_length ms) k) : Eq Nat (Nat.succ k) (list_length (ListType.cons KExpr m ms)) := Eq.trans Nat (Nat.succ k) (Nat.succ (list_length ms)) (list_length (ListType.cons KExpr m ms)) (Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) k (list_length ms) (Eq.symm Nat (list_length ms) k hk)) (Eq.symm Nat (list_length (ListType.cons KExpr m ms)) (Nat.succ (list_length ms)) (list_length_cons m ms))",
            "k+1 = |cons m ms| (cong succ over hk + list_length_cons). SnSchema B4c (mapLT_instIter_prefix helper).",
        )?;
        self.add_recursive_def(
            "def prefix_len_na (m : KExpr) (ms : ListType KExpr) (fields : ListType KExpr) (r : Nat) (k : Nat) (hk : Eq Nat (list_length ms) k) (hfl : Eq Nat (list_length fields) r) : Eq Nat (Nat.succ (Nat.add k r)) (list_length (ListType.cons KExpr m (list_append ms fields))) := Eq.trans Nat (Nat.succ (Nat.add k r)) (Nat.succ (list_length (list_append ms fields))) (list_length (ListType.cons KExpr m (list_append ms fields))) (Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (Nat.add k r) (list_length (list_append ms fields)) (Eq.symm Nat (list_length (list_append ms fields)) (Nat.add k r) (Eq.trans Nat (list_length (list_append ms fields)) (Nat.add (list_length ms) (list_length fields)) (Nat.add k r) (list_append_length ms fields) (Eq.trans Nat (Nat.add (list_length ms) (list_length fields)) (Nat.add k (list_length fields)) (Nat.add k r) (Eq.cong Nat Nat (fun (w : Nat) => Nat.add w (list_length fields)) (list_length ms) k hk) (Eq.cong Nat Nat (fun (w : Nat) => Nat.add k w) (list_length fields) r hfl))))) (Eq.symm Nat (list_length (ListType.cons KExpr m (list_append ms fields))) (Nat.succ (list_length (list_append ms fields))) (list_length_cons m (list_append ms fields)))",
            "succ(k+r) = |cons m (ms++fields)| (list_append_length + hk/hfl + list_length_cons). SnSchema B4c (instIter_bvar index bridge for mapLT_instIter_prefix).",
        )?;
        self.add_recursive_def(
            "def prefix_lt_sk (m : KExpr) (ms : ListType KExpr) (fields : ListType KExpr) (r : Nat) (k : Nat) (q : Nat) (hq : Lt q (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r k) (Nat.succ k))))) : Lt q (Nat.succ k) := Eq.substType Nat (fun (N : Nat) => Lt q N) (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r k) (Nat.succ k)))) (Nat.succ k) (prefix_len_eq m ms fields r k) hq",
            "Lt q |mapLT F (bvarSeq (r+k)(k+1))| -> Lt q (k+1) (substType via prefix_len_eq). SnSchema B4c (mapLT_instIter_prefix helper).",
        )?;
        self.add_recursive_def(
            "def mapLT_instIter_prefix (m : KExpr) (ms : ListType KExpr) (fields : ListType KExpr) (r : Nat) (k : Nat) (hfl : Eq Nat (list_length fields) r) (hk : Eq Nat (list_length ms) k) : Eq (ListType KExpr) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r k) (Nat.succ k))) (ListType.cons KExpr m ms) := lget_ext (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r k) (Nat.succ k))) (ListType.cons KExpr m ms) (Eq.trans Nat (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r k) (Nat.succ k)))) (Nat.succ k) (list_length (ListType.cons KExpr m ms)) (prefix_len_eq m ms fields r k) (prefix_len_eq2 m ms k hk)) (fun (q : Nat) (hq : Lt q (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r k) (Nat.succ k))))) => lget_at_ltb (ListType.cons KExpr m ms) q (Eq.trans Bool (nat_lt_b q (list_length (ListType.cons KExpr m ms))) (nat_lt_b q (Nat.succ k)) Bool.true (Eq.cong Nat Bool (fun (w : Nat) => nat_lt_b q w) (list_length (ListType.cons KExpr m ms)) (Nat.succ k) (Eq.symm Nat (Nat.succ k) (list_length (ListType.cons KExpr m ms)) (prefix_len_eq2 m ms k hk))) (nat_lt_to_ltb q (Nat.succ k) (prefix_lt_sk m ms fields r k q hq))) (Eq (OptionType KExpr) (lget (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r k) (Nat.succ k))) q) (lget (ListType.cons KExpr m ms) q)) (fun (cq : KExpr) (hcq : Eq (OptionType KExpr) (lget (ListType.cons KExpr m ms) q) (OptionType.some KExpr cq)) => Eq.trans (OptionType KExpr) (lget (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r k) (Nat.succ k))) q) (OptionType.some KExpr cq) (lget (ListType.cons KExpr m ms) q) (Eq.trans (OptionType KExpr) (lget (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r k) (Nat.succ k))) q) (OptionType.some KExpr (instIter (KExpr.bvar (Nat.sub (Nat.add r k) q)) (ListType.cons KExpr m (list_append ms fields)))) (OptionType.some KExpr cq) (lget_mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r k) (Nat.succ k)) q (KExpr.bvar (Nat.sub (Nat.add r k) q)) (bvarSeq_lget (Nat.succ k) (Nat.add r k) q (nat_lt_to_ltb q (Nat.succ k) (prefix_lt_sk m ms fields r k q hq)))) (Eq.cong KExpr (OptionType KExpr) (fun (w : KExpr) => OptionType.some KExpr w) (instIter (KExpr.bvar (Nat.sub (Nat.add r k) q)) (ListType.cons KExpr m (list_append ms fields))) cq (instIter_bvar (ListType.cons KExpr m (list_append ms fields)) (Nat.sub (Nat.add r k) q) q cq (Eq.trans Nat (Nat.add (Nat.succ (Nat.sub (Nat.add r k) q)) q) (Nat.succ (Nat.add k r)) (list_length (ListType.cons KExpr m (list_append ms fields))) (prefix_index_eq r k q (Nat.add r k) (Eq.refl Nat (Nat.add r k)) (le_trans q k (Nat.add r k) (lt_succ_to_le q k (prefix_lt_sk m ms fields r k q hq)) (le_add_self_right r k))) (prefix_len_na m ms fields r k hk hfl)) (lget_cons_append_some m ms fields cq q hcq)))) (Eq.symm (OptionType KExpr) (lget (ListType.cons KExpr m ms) q) (OptionType.some KExpr cq) hcq)))",
            "mapLT (fun t => instIter t (m :: ms ++ fields)) (bvarSeq (r+k) (k+1)) = cons m ms when |fields|=r, |ms|=k. Via lget_ext: length (prefix_len_eq+prefix_len_eq2); per-index q<k+1, instIter (bvar (r+k-q)) .. = (m::ms)[q] via lget_mapLT o bvarSeq_lget + instIter_bvar (prefix_index_eq index + lget_cons_append_some lookup), witness from lget_at_ltb. SnSchema B4c.",
        )?;
        // ── B4c: reccalls_step — the per-index KExpr equality feeding
        //    mapLT_instIter_recCalls. One recursive-call spine, instantiated over
        //    `m :: ms ++ fields`, resolves to `genRecApp fam sig u m ms fp`.
        //    instIter_apply_spine distributes instIter through the spine;
        //    instIter_const fixes the closed genRecC head; mapLT_append splits the
        //    prefix/field spine; mapLT_instIter_prefix -> `m::ms`; instIter_bvar_field
        //    -> fp; final rfl (list_append (cons m ms)[fp] ≡ cons m (ms++[fp]) = genRecApp).
        self.add_recursive_def(
            "def reccalls_step (fam : Name) (sig : ListType Nat) (u : Level) (m : KExpr) (ms : ListType KExpr) (fields : ListType KExpr) (r : Nat) (p : Nat) (fp : KExpr) (hfl : Eq Nat (list_length fields) r) (hms : Eq Nat (list_length ms) (sigLength sig)) (hp : Lt p r) (hfp : Eq (OptionType KExpr) (lget fields p) (OptionType.some KExpr fp)) : Eq KExpr (instIter (apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr))) (genRecC fam sig u)) (ListType.cons KExpr m (list_append ms fields))) (genRecApp fam sig u m ms fp) := Eq.trans KExpr (instIter (apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr))) (genRecC fam sig u)) (ListType.cons KExpr m (list_append ms fields))) (apply_spine (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr)))) (instIter (genRecC fam sig u) (ListType.cons KExpr m (list_append ms fields)))) (genRecApp fam sig u m ms fp) (instIter_apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr))) (genRecC fam sig u) (ListType.cons KExpr m (list_append ms fields))) (Eq.trans KExpr (apply_spine (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr)))) (instIter (genRecC fam sig u) (ListType.cons KExpr m (list_append ms fields)))) (apply_spine (list_append (ListType.cons KExpr m ms) (ListType.cons KExpr fp (ListType.nil KExpr))) (genRecC fam sig u)) (genRecApp fam sig u m ms fp) (Eq.trans KExpr (apply_spine (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr)))) (instIter (genRecC fam sig u) (ListType.cons KExpr m (list_append ms fields)))) (apply_spine (list_append (ListType.cons KExpr m ms) (ListType.cons KExpr fp (ListType.nil KExpr))) (instIter (genRecC fam sig u) (ListType.cons KExpr m (list_append ms fields)))) (apply_spine (list_append (ListType.cons KExpr m ms) (ListType.cons KExpr fp (ListType.nil KExpr))) (genRecC fam sig u)) (Eq.cong (ListType KExpr) KExpr (fun (A : ListType KExpr) => apply_spine A (instIter (genRecC fam sig u) (ListType.cons KExpr m (list_append ms fields)))) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr)))) (list_append (ListType.cons KExpr m ms) (ListType.cons KExpr fp (ListType.nil KExpr))) (Eq.trans (ListType KExpr) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr)))) (list_append (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig)))) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr)))) (list_append (ListType.cons KExpr m ms) (ListType.cons KExpr fp (ListType.nil KExpr))) (mapLT_append (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr))) (Eq.trans (ListType KExpr) (list_append (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig)))) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr)))) (list_append (ListType.cons KExpr m ms) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr)))) (list_append (ListType.cons KExpr m ms) (ListType.cons KExpr fp (ListType.nil KExpr))) (Eq.cong (ListType KExpr) (ListType KExpr) (fun (LL : ListType KExpr) => list_append LL (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr)))) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig)))) (ListType.cons KExpr m ms) (mapLT_instIter_prefix m ms fields r (sigLength sig) hfl hms)) (Eq.cong (ListType KExpr) (ListType KExpr) (fun (RR : ListType KExpr) => list_append (ListType.cons KExpr m ms) RR) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr))) (ListType.cons KExpr fp (ListType.nil KExpr)) (Eq.cong KExpr (ListType KExpr) (fun (z : KExpr) => ListType.cons KExpr z (ListType.nil KExpr)) (instIter (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.cons KExpr m (list_append ms fields))) fp (instIter_bvar_field m ms fields r p fp hfl hp hfp)))))) (Eq.cong KExpr KExpr (fun (H : KExpr) => apply_spine (list_append (ListType.cons KExpr m ms) (ListType.cons KExpr fp (ListType.nil KExpr))) H) (instIter (genRecC fam sig u) (ListType.cons KExpr m (list_append ms fields))) (genRecC fam sig u) (instIter_const (ListType.cons KExpr m (list_append ms fields)) (genRecName fam sig) (ListType.cons Level u (ListType.nil Level))))) (Eq.refl KExpr (genRecApp fam sig u m ms fp)))",
            "instIter (apply_spine (bvarSeq(r+|sig|)(|sig|+1) ++ [bvar(r-1-p)]) genRecC) (m::ms++fields) = genRecApp fam sig u m ms fp. instIter_apply_spine + instIter_const + mapLT_append + mapLT_instIter_prefix + instIter_bvar_field + rfl. SnSchema B4c (mapLT_instIter_recCalls crux).",
        )?;
        self.add_recursive_def(
            "def reccalls_len (fam : Name) (sig : ListType Nat) (u : Level) (m : KExpr) (ms : ListType KExpr) (fields : ListType KExpr) (r : Nat) : Eq Nat (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) r := Eq.trans Nat (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) (list_length (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) r (mapLT_length (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) (Eq.trans Nat (list_length (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) (list_length (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) r (mapLT_length (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) (bvarSeq_length r (Nat.sub r (Nat.succ Nat.zero))))",
            "|mapLT F (mapLT G (bvarSeq (r-1) r))| = r (3x mapLT_length/bvarSeq_length). SnSchema B4c (mapLT_instIter_recCalls helper).",
        )?;
        self.add_recursive_def(
            "def reccalls_lt (fam : Name) (sig : ListType Nat) (u : Level) (m : KExpr) (ms : ListType KExpr) (fields : ListType KExpr) (r : Nat) (p : Nat) (hp : Lt p (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))))) : Lt p r := Eq.substType Nat (fun (N : Nat) => Lt p N) (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) r (reccalls_len fam sig u m ms fields r) hp",
            "Lt p |Source| -> Lt p r (substType via reccalls_len). SnSchema B4c (mapLT_instIter_recCalls helper).",
        )?;
        self.add_recursive_def(
            "def mapLT_instIter_recCalls (fam : Name) (sig : ListType Nat) (u : Level) (m : KExpr) (ms : ListType KExpr) (fields : ListType KExpr) (r : Nat) (hms : Eq Nat (list_length ms) (sigLength sig)) (hfl : Eq Nat (list_length fields) r) : Eq (ListType KExpr) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields) := lget_ext (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields) (Eq.trans Nat (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) r (list_length (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields)) (reccalls_len fam sig u m ms fields r) (Eq.symm Nat (list_length (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields)) r (Eq.trans Nat (list_length (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields)) (list_length fields) r (mapLT_length (fun (x : KExpr) => genRecApp fam sig u m ms x) fields) hfl))) (fun (p : Nat) (hp : Lt p (list_length (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))))) => lget_at_ltb fields p (Eq.trans Bool (nat_lt_b p (list_length fields)) (nat_lt_b p r) Bool.true (Eq.cong Nat Bool (fun (w : Nat) => nat_lt_b p w) (list_length fields) r hfl) (nat_lt_to_ltb p r (reccalls_lt fam sig u m ms fields r p hp))) (Eq (OptionType KExpr) (lget (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) p) (lget (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields) p)) (fun (fp : KExpr) (hfp : Eq (OptionType KExpr) (lget fields p) (OptionType.some KExpr fp)) => Eq.trans (OptionType KExpr) (lget (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) p) (OptionType.some KExpr (genRecApp fam sig u m ms fp)) (lget (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields) p) (Eq.trans (OptionType KExpr) (lget (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) p) (OptionType.some KExpr (instIter (apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr))) (genRecC fam sig u)) (ListType.cons KExpr m (list_append ms fields)))) (OptionType.some KExpr (genRecApp fam sig u m ms fp)) (lget_mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) p (apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr))) (genRecC fam sig u)) (lget_mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) p (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (bvarSeq_lget r (Nat.sub r (Nat.succ Nat.zero)) p (nat_lt_to_ltb p r (reccalls_lt fam sig u m ms fields r p hp))))) (Eq.cong KExpr (OptionType KExpr) (fun (w : KExpr) => OptionType.some KExpr w) (instIter (apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.succ (sigLength sig))) (ListType.cons KExpr (KExpr.bvar (Nat.sub (Nat.sub r (Nat.succ Nat.zero)) p)) (ListType.nil KExpr))) (genRecC fam sig u)) (ListType.cons KExpr m (list_append ms fields))) (genRecApp fam sig u m ms fp) (reccalls_step fam sig u m ms fields r p fp hfl hms (reccalls_lt fam sig u m ms fields r p hp) hfp))) (Eq.symm (OptionType KExpr) (lget (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields) p) (OptionType.some KExpr (genRecApp fam sig u m ms fp)) (lget_mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields p fp hfp))))",
            "mapLT (fun t => instIter t (m::ms++fields)) (mapLT (recCall-spine) (bvarSeq (r-1) r)) = mapLT (genRecApp fam sig u m ms) fields when |ms|=|sig|, |fields|=r. Via lget_ext (reccalls_len length); per-index p<r: source resolves via lget_mapLT o lget_mapLT o bvarSeq_lget + reccalls_step, target via lget_mapLT, witness lget_at_ltb. SnSchema B4c.",
        )?;
        // `lget xs p = some x` => `Lt p |xs|` (the inductive Lt, for the minor-slot
        // index arithmetic in genRecRhs_instIter). ListType.rec on xs (nil absurd via
        // option_none_ne_some), Nat.rec on p; Lt built from Lt.zero_lt_succ /
        // Lt.succ_lt_succ, substType-pinned to `list_length (cons ..)` via list_length_cons.
        self.add_recursive_def(
            "def lget_lt (xs : ListType KExpr) : forall (p : Nat) (x : KExpr), Eq (OptionType KExpr) (lget xs p) (OptionType.some KExpr x) -> Lt p (list_length xs) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (p : Nat) (x : KExpr), Eq (OptionType KExpr) (lget l p) (OptionType.some KExpr x) -> Lt p (list_length l)) (fun (p : Nat) (x : KExpr) (h : Eq (OptionType KExpr) (lget (ListType.nil KExpr) p) (OptionType.some KExpr x)) => Eq.substType (OptionType KExpr) (fun (o : OptionType KExpr) => OptionType.rec KExpr (fun (_ : OptionType KExpr) => Type) Nat (fun (_ : KExpr) => Lt p (list_length (ListType.nil KExpr))) o) (OptionType.none KExpr) (OptionType.some KExpr x) h Nat.zero) (fun (a : KExpr) (T : ListType KExpr) (ih : forall (p : Nat) (x : KExpr), Eq (OptionType KExpr) (lget T p) (OptionType.some KExpr x) -> Lt p (list_length T)) => fun (p : Nat) => Nat.rec (fun (pp : Nat) => forall (x : KExpr), Eq (OptionType KExpr) (lget (ListType.cons KExpr a T) pp) (OptionType.some KExpr x) -> Lt pp (list_length (ListType.cons KExpr a T))) (fun (x : KExpr) (h : Eq (OptionType KExpr) (lget (ListType.cons KExpr a T) Nat.zero) (OptionType.some KExpr x)) => Eq.substType Nat (fun (N : Nat) => Lt Nat.zero N) (Nat.succ (list_length T)) (list_length (ListType.cons KExpr a T)) (Eq.symm Nat (list_length (ListType.cons KExpr a T)) (Nat.succ (list_length T)) (list_length_cons a T)) (Lt.zero_lt_succ (list_length T))) (fun (p0 : Nat) (_ : forall (x : KExpr), Eq (OptionType KExpr) (lget (ListType.cons KExpr a T) p0) (OptionType.some KExpr x) -> Lt p0 (list_length (ListType.cons KExpr a T))) (x : KExpr) (h : Eq (OptionType KExpr) (lget (ListType.cons KExpr a T) (Nat.succ p0)) (OptionType.some KExpr x)) => Eq.substType Nat (fun (N : Nat) => Lt (Nat.succ p0) N) (Nat.succ (list_length T)) (list_length (ListType.cons KExpr a T)) (Eq.symm Nat (list_length (ListType.cons KExpr a T)) (Nat.succ (list_length T)) (list_length_cons a T)) (Lt.succ_lt_succ p0 (list_length T) (ih p0 x (Eq.trans (OptionType KExpr) (lget T p0) (lget (ListType.cons KExpr a T) (Nat.succ p0)) (OptionType.some KExpr x) (Eq.symm (OptionType KExpr) (lget (ListType.cons KExpr a T) (Nat.succ p0)) (lget T p0) (lget_cons_succ a T p0)) h)))) p) xs",
            "lget xs p = some x => Lt p |xs| (ListType.rec on xs, Nat.rec on p; Lt.zero/succ_lt_succ, list_length_cons pin). SnSchema B4c (genRecRhs_instIter minor-slot helper).",
        )?;
        // Minor-slot index arithmetic for instIter_bvar in genRecRhs_instIter:
        // succ(r + ((sl-1)-j)) + succ j = succ(sl + r) when Lt j sl. Same chain
        // shape as field_index_eq. Feeds the mj minor slot (bvar (r+(sl-1-j))).
        self.add_recursive_def(
            "def minor_index_eq (r : Nat) (sl : Nat) (j : Nat) (hlt : Lt j sl) : Eq Nat (Nat.add (Nat.succ (Nat.add r (Nat.sub (Nat.sub sl (Nat.succ Nat.zero)) j))) (Nat.succ j)) (Nat.succ (Nat.add sl r)) := Eq.trans Nat (Nat.add (Nat.succ (Nat.add r (Nat.sub (Nat.sub sl (Nat.succ Nat.zero)) j))) (Nat.succ j)) (Nat.succ (Nat.add (Nat.add r (Nat.sub (Nat.sub sl (Nat.succ Nat.zero)) j)) (Nat.succ j))) (Nat.succ (Nat.add sl r)) (nat_succ_add (Nat.add r (Nat.sub (Nat.sub sl (Nat.succ Nat.zero)) j)) (Nat.succ j)) (Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (Nat.add (Nat.add r (Nat.sub (Nat.sub sl (Nat.succ Nat.zero)) j)) (Nat.succ j)) (Nat.add sl r) (Eq.trans Nat (Nat.add (Nat.add r (Nat.sub (Nat.sub sl (Nat.succ Nat.zero)) j)) (Nat.succ j)) (Nat.succ (Nat.add (Nat.add r (Nat.sub (Nat.sub sl (Nat.succ Nat.zero)) j)) j)) (Nat.add sl r) (nat_add_succ_right (Nat.add r (Nat.sub (Nat.sub sl (Nat.succ Nat.zero)) j)) j) (Eq.trans Nat (Nat.succ (Nat.add (Nat.add r (Nat.sub (Nat.sub sl (Nat.succ Nat.zero)) j)) j)) (Nat.succ (Nat.add r (Nat.sub sl (Nat.succ Nat.zero)))) (Nat.add sl r) (Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (Nat.add (Nat.add r (Nat.sub (Nat.sub sl (Nat.succ Nat.zero)) j)) j) (Nat.add r (Nat.sub sl (Nat.succ Nat.zero))) (Eq.trans Nat (Nat.add (Nat.add r (Nat.sub (Nat.sub sl (Nat.succ Nat.zero)) j)) j) (Nat.add r (Nat.add (Nat.sub (Nat.sub sl (Nat.succ Nat.zero)) j) j)) (Nat.add r (Nat.sub sl (Nat.succ Nat.zero))) (nat_add_assoc r (Nat.sub (Nat.sub sl (Nat.succ Nat.zero)) j) j) (Eq.cong Nat Nat (fun (w : Nat) => Nat.add r w) (Nat.add (Nat.sub (Nat.sub sl (Nat.succ Nat.zero)) j) j) (Nat.sub sl (Nat.succ Nat.zero)) (nat_sub_add_cancel j (Nat.sub sl (Nat.succ Nat.zero)) (lt_succ_to_le j (Nat.sub sl (Nat.succ Nat.zero)) (Eq.substType Nat (fun (N : Nat) => Lt j N) sl (Nat.succ (Nat.sub sl (Nat.succ Nat.zero))) (Eq.symm Nat (Nat.succ (Nat.sub sl (Nat.succ Nat.zero))) sl (nat_succ_sub1_of_lt j sl hlt)) hlt)))))) (Eq.trans Nat (Nat.succ (Nat.add r (Nat.sub sl (Nat.succ Nat.zero)))) (Nat.add r sl) (Nat.add sl r) (Eq.trans Nat (Nat.succ (Nat.add r (Nat.sub sl (Nat.succ Nat.zero)))) (Nat.add r (Nat.succ (Nat.sub sl (Nat.succ Nat.zero)))) (Nat.add r sl) (Eq.symm Nat (Nat.add r (Nat.succ (Nat.sub sl (Nat.succ Nat.zero)))) (Nat.succ (Nat.add r (Nat.sub sl (Nat.succ Nat.zero)))) (nat_add_succ_right r (Nat.sub sl (Nat.succ Nat.zero)))) (Eq.cong Nat Nat (fun (w : Nat) => Nat.add r w) (Nat.succ (Nat.sub sl (Nat.succ Nat.zero))) sl (nat_succ_sub1_of_lt j sl hlt))) (nat_add_comm r sl)))))",
            "succ(r + ((sl-1)-j)) + succ j = succ(sl + r) when Lt j sl. nat_succ_add + nat_add_succ_right + nat_add_assoc + nat_sub_add_cancel [Le j (sl-1) via lt_succ_to_le o substType(nat_succ_sub1_of_lt)] + nat_add_comm. SnSchema B4c (genRecRhs_instIter minor slot).",
        )?;
        // ── B4c THE CRUX: genRecRhs_instIter. instIter of the generic rule-rhs BODY
        //    at the spine `[m] ++ ms ++ fields` yields the generic contractum with
        //    the original m/ms/fields. instIter_apply_spine distributes; mapLT_append
        //    splits the field-prefix from the recursive-call prefix;
        //    mapLT_instIter_fields resolves the fields, mapLT_instIter_recCalls the
        //    recursive calls; the mj minor slot resolves via instIter_bvar
        //    (minor_index_eq index + lget_cons_succ/lget_append_lt lookup, j<|ms|
        //    from lget_lt). Final rfl (genContractum def). Guide L5881.
        self.add_recursive_def(
            "def genRecRhs_instIter (fam : Name) (sig : ListType Nat) (u : Level) (j : Nat) (r : Nat) (m : KExpr) (mj : KExpr) (ms : ListType KExpr) (fields : ListType KExpr) (hms : Eq Nat (list_length ms) (sigLength sig)) (hj : Eq (OptionType KExpr) (lget ms j) (OptionType.some KExpr mj)) (hfl : Eq Nat (list_length fields) r) : Eq KExpr (instIter (genRecRhsBody fam sig u j r) (ListType.cons KExpr m (list_append ms fields))) (genContractum fam sig u m ms mj fields) := Eq.trans KExpr (instIter (genRecRhsBody fam sig u j r) (ListType.cons KExpr m (list_append ms fields))) (apply_spine (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (list_append (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) (instIter (KExpr.bvar (Nat.add r (Nat.sub (Nat.sub (sigLength sig) (Nat.succ Nat.zero)) j))) (ListType.cons KExpr m (list_append ms fields)))) (genContractum fam sig u m ms mj fields) (instIter_apply_spine (list_append (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) (KExpr.bvar (Nat.add r (Nat.sub (Nat.sub (sigLength sig) (Nat.succ Nat.zero)) j))) (ListType.cons KExpr m (list_append ms fields))) (Eq.trans KExpr (apply_spine (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (list_append (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) (instIter (KExpr.bvar (Nat.add r (Nat.sub (Nat.sub (sigLength sig) (Nat.succ Nat.zero)) j))) (ListType.cons KExpr m (list_append ms fields)))) (apply_spine (list_append fields (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields)) mj) (genContractum fam sig u m ms mj fields) (Eq.trans KExpr (apply_spine (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (list_append (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) (instIter (KExpr.bvar (Nat.add r (Nat.sub (Nat.sub (sigLength sig) (Nat.succ Nat.zero)) j))) (ListType.cons KExpr m (list_append ms fields)))) (apply_spine (list_append fields (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields)) (instIter (KExpr.bvar (Nat.add r (Nat.sub (Nat.sub (sigLength sig) (Nat.succ Nat.zero)) j))) (ListType.cons KExpr m (list_append ms fields)))) (apply_spine (list_append fields (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields)) mj) (Eq.cong (ListType KExpr) KExpr (fun (A : ListType KExpr) => apply_spine A (instIter (KExpr.bvar (Nat.add r (Nat.sub (Nat.sub (sigLength sig) (Nat.succ Nat.zero)) j))) (ListType.cons KExpr m (list_append ms fields)))) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (list_append (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) (list_append fields (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields)) (Eq.trans (ListType KExpr) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (list_append (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) (list_append (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) (list_append fields (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields)) (mapLT_append (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) (Eq.trans (ListType KExpr) (list_append (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) (list_append fields (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) (list_append fields (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields)) (Eq.cong (ListType KExpr) (ListType KExpr) (fun (LL : ListType KExpr) => list_append LL (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) fields (mapLT_instIter_fields m ms fields r hfl)) (Eq.cong (ListType KExpr) (ListType KExpr) (fun (RR : ListType KExpr) => list_append fields RR) (mapLT (fun (t : KExpr) => instIter t (ListType.cons KExpr m (list_append ms fields))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (ListType.cons KExpr x (ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields) (mapLT_instIter_recCalls fam sig u m ms fields r hms hfl))))) (Eq.cong KExpr KExpr (fun (H : KExpr) => apply_spine (list_append fields (mapLT (fun (x : KExpr) => genRecApp fam sig u m ms x) fields)) H) (instIter (KExpr.bvar (Nat.add r (Nat.sub (Nat.sub (sigLength sig) (Nat.succ Nat.zero)) j))) (ListType.cons KExpr m (list_append ms fields))) mj (instIter_bvar (ListType.cons KExpr m (list_append ms fields)) (Nat.add r (Nat.sub (Nat.sub (sigLength sig) (Nat.succ Nat.zero)) j)) (Nat.succ j) mj (Eq.trans Nat (Nat.add (Nat.succ (Nat.add r (Nat.sub (Nat.sub (sigLength sig) (Nat.succ Nat.zero)) j))) (Nat.succ j)) (Nat.succ (Nat.add (sigLength sig) r)) (list_length (ListType.cons KExpr m (list_append ms fields))) (minor_index_eq r (sigLength sig) j (Eq.substType Nat (fun (N : Nat) => Lt j N) (list_length ms) (sigLength sig) hms (lget_lt ms j mj hj))) (Eq.trans Nat (Nat.succ (Nat.add (sigLength sig) r)) (Nat.succ (list_length (list_append ms fields))) (list_length (ListType.cons KExpr m (list_append ms fields))) (Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (Nat.add (sigLength sig) r) (list_length (list_append ms fields)) (Eq.symm Nat (list_length (list_append ms fields)) (Nat.add (sigLength sig) r) (Eq.trans Nat (list_length (list_append ms fields)) (Nat.add (list_length ms) (list_length fields)) (Nat.add (sigLength sig) r) (list_append_length ms fields) (Eq.trans Nat (Nat.add (list_length ms) (list_length fields)) (Nat.add (sigLength sig) (list_length fields)) (Nat.add (sigLength sig) r) (Eq.cong Nat Nat (fun (w : Nat) => Nat.add w (list_length fields)) (list_length ms) (sigLength sig) hms) (Eq.cong Nat Nat (fun (w : Nat) => Nat.add (sigLength sig) w) (list_length fields) r hfl))))) (Eq.symm Nat (list_length (ListType.cons KExpr m (list_append ms fields))) (Nat.succ (list_length (list_append ms fields))) (list_length_cons m (list_append ms fields))))) (Eq.trans (OptionType KExpr) (lget (ListType.cons KExpr m (list_append ms fields)) (Nat.succ j)) (lget (list_append ms fields) j) (OptionType.some KExpr mj) (lget_cons_succ m (list_append ms fields) j) (lget_append_lt fields ms j mj hj))))) (Eq.refl KExpr (genContractum fam sig u m ms mj fields)))",
            "instIter genRecRhsBody ([m]++ms++fields) = genContractum m ms mj fields when |ms|=|sig|, lget ms j = some mj, |fields|=r. THE CRUX: instIter_apply_spine + mapLT_append + mapLT_instIter_fields + mapLT_instIter_recCalls + instIter_bvar(minor_index_eq + lget_cons_succ/lget_append_lt, lget_lt) + rfl. SnSchema B4c.",
        )?;

        // ── B4c bridge: listGet_eq_lget. GenRecContract.rule carries the mj minor
        //    lookup as listGet (structural Nat.rec on the index); the crux
        //    genRecRhs_instIter wants it as lget (Bool.rec on nat_is_zero + pred).
        //    They agree pointwise but at different head symbols, so they are NOT
        //    defeq for opaque ms/j — prove Eq by ListType.rec on xs, Nat.rec on j
        //    (every arm collapses by refl: nil->none, cons/0->some a, cons/succ->tail).
        self.add_recursive_def(
            "def listGet_eq_lget (xs : ListType KExpr) : forall (j : Nat), Eq (OptionType KExpr) (listGet xs j) (lget xs j) := ListType.rec KExpr (fun (l : ListType KExpr) => forall (j : Nat), Eq (OptionType KExpr) (listGet l j) (lget l j)) (fun (j : Nat) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (a : KExpr) (rest : ListType KExpr) (ih : forall (j : Nat), Eq (OptionType KExpr) (listGet rest j) (lget rest j)) => fun (j : Nat) => Nat.rec (fun (jj : Nat) => Eq (OptionType KExpr) (listGet (ListType.cons KExpr a rest) jj) (lget (ListType.cons KExpr a rest) jj)) (Eq.refl (OptionType KExpr) (OptionType.some KExpr a)) (fun (j0 : Nat) (_ : Eq (OptionType KExpr) (listGet (ListType.cons KExpr a rest) j0) (lget (ListType.cons KExpr a rest) j0)) => ih j0) j) xs",
            "listGet xs j = lget xs j (structural-index vs nat_is_zero/pred lookups agree; ListType.rec + Nat.rec, all arms refl). Bridges GenRecContract.rule's listGet hj to genRecRhs_instIter's lget hj. SnSchema B4c bridge.",
        )?;

        // ── B4c FINAL: genRecContract_steps. Every object-level generic-recursor
        //    iota rule (GenRecContract fam sig u lhs rhs) is realized as a real
        //    multi-step genSteps reduction lhs ⟶* rhs. Mirrors the concrete
        //    natRecContract_steps (natrec.rs) via GenRecContract.rec's single `rule`
        //    case: one head iota step (iota_fires_gen, definitionally an iota_step,
        //    wrapped genIotaCong.head/genStep.iota) landing at the pre-beta contractum
        //    apply_spine fields (apply_spine [m]++ms genRecRhs), then a β* telescope
        //    (lamTel_beta — already in genSteps) transported through genRecRhs_eq_lamTel
        //    + apply_spine_append at the start and the CRUX genRecRhs_instIter at the
        //    end. The telescope-length obligation hlen: |[m::ms]++fields| = |genRecDoms|
        //    via list_append_length + minorTys_length + replicateLT_length + nat_succ_add.
        //    THE Nat.rec-scale computation-fidelity theorem, generalized. Guide L6011.
        self.add_recursive_def(
            "def genRecContract_steps (fam : Name) (sig : ListType Nat) (u : Level) (e : KExpr) (e2 : KExpr) (h : GenRecContract fam sig u e e2) : genSteps fam sig u e e2 := GenRecContract.rec fam sig u (fun (e0 : KExpr) (e0b : KExpr) (_ : GenRecContract fam sig u e0 e0b) => genSteps fam sig u e0 e0b) (fun (j : Nat) (r : Nat) (m : KExpr) (mj : KExpr) (ms : ListType KExpr) (fields : ListType KExpr) (hjr : Eq (OptionType Nat) (sigGet sig j) (OptionType.some Nat r)) (hms : Eq Nat (list_length ms) (sigLength sig)) (hj : Eq (OptionType KExpr) (listGet ms j) (OptionType.some KExpr mj)) (hfl : Eq Nat (list_length fields) r) => genSteps.step fam sig u (genRecApp fam sig u m ms (ctorApp fam j fields)) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) (genContractum fam sig u m ms mj fields) (genStep.iota fam sig u (genRecApp fam sig u m ms (ctorApp fam j fields)) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) (genIotaCong.head fam sig u (genRecApp fam sig u m ms (ctorApp fam j fields)) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) (iota_fires_gen fam sig u m ms j r fields hms hjr hfl))) (Eq.substType KExpr (fun (S : KExpr) => genSteps fam sig u S (genContractum fam sig u m ms mj fields)) (apply_spine (list_append (ListType.cons KExpr m ms) fields) (lamTel (genRecDoms fam sig u r) (genRecRhsBody fam sig u j r))) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) (Eq.trans KExpr (apply_spine (list_append (ListType.cons KExpr m ms) fields) (lamTel (genRecDoms fam sig u r) (genRecRhsBody fam sig u j r))) (apply_spine (list_append (ListType.cons KExpr m ms) fields) (genRecRhs fam sig u j r)) (apply_spine fields (apply_spine (ListType.cons KExpr m ms) (genRecRhs fam sig u j r))) (Eq.cong KExpr KExpr (fun (X : KExpr) => apply_spine (list_append (ListType.cons KExpr m ms) fields) X) (lamTel (genRecDoms fam sig u r) (genRecRhsBody fam sig u j r)) (genRecRhs fam sig u j r) (Eq.symm KExpr (genRecRhs fam sig u j r) (lamTel (genRecDoms fam sig u r) (genRecRhsBody fam sig u j r)) (genRecRhs_eq_lamTel fam sig u j r))) (apply_spine_append (ListType.cons KExpr m ms) fields (genRecRhs fam sig u j r))) (Eq.substType KExpr (fun (E : KExpr) => genSteps fam sig u (apply_spine (list_append (ListType.cons KExpr m ms) fields) (lamTel (genRecDoms fam sig u r) (genRecRhsBody fam sig u j r))) E) (instIter (genRecRhsBody fam sig u j r) (ListType.cons KExpr m (list_append ms fields))) (genContractum fam sig u m ms mj fields) (genRecRhs_instIter fam sig u j r m mj ms fields hms (Eq.trans (OptionType KExpr) (lget ms j) (listGet ms j) (OptionType.some KExpr mj) (Eq.symm (OptionType KExpr) (listGet ms j) (lget ms j) (listGet_eq_lget ms j)) hj) hfl) (lamTel_beta fam sig u (list_append (ListType.cons KExpr m ms) fields) (genRecDoms fam sig u r) (genRecRhsBody fam sig u j r) (Eq.trans Nat (list_length (list_append (ListType.cons KExpr m ms) fields)) (Nat.succ (Nat.add (sigLength sig) r)) (list_length (genRecDoms fam sig u r)) (Eq.trans Nat (list_length (list_append (ListType.cons KExpr m ms) fields)) (Nat.add (Nat.succ (list_length ms)) (list_length fields)) (Nat.succ (Nat.add (sigLength sig) r)) (list_append_length (ListType.cons KExpr m ms) fields) (Eq.trans Nat (Nat.add (Nat.succ (list_length ms)) (list_length fields)) (Nat.add (Nat.succ (sigLength sig)) r) (Nat.succ (Nat.add (sigLength sig) r)) (Eq.trans Nat (Nat.add (Nat.succ (list_length ms)) (list_length fields)) (Nat.add (Nat.succ (list_length ms)) r) (Nat.add (Nat.succ (sigLength sig)) r) (Eq.cong Nat Nat (fun (w : Nat) => Nat.add (Nat.succ (list_length ms)) w) (list_length fields) r hfl) (Eq.cong Nat Nat (fun (w : Nat) => Nat.add (Nat.succ w) r) (list_length ms) (sigLength sig) hms)) (nat_succ_add (sigLength sig) r))) (Eq.symm Nat (list_length (genRecDoms fam sig u r)) (Nat.succ (Nat.add (sigLength sig) r)) (Eq.cong Nat Nat (fun (w : Nat) => Nat.succ w) (list_length (list_append (minorTys fam Nat.zero sig) (replicateLT r (famTypeC fam)))) (Nat.add (sigLength sig) r) (Eq.trans Nat (list_length (list_append (minorTys fam Nat.zero sig) (replicateLT r (famTypeC fam)))) (Nat.add (list_length (minorTys fam Nat.zero sig)) (list_length (replicateLT r (famTypeC fam)))) (Nat.add (sigLength sig) r) (list_append_length (minorTys fam Nat.zero sig) (replicateLT r (famTypeC fam))) (Eq.trans Nat (Nat.add (list_length (minorTys fam Nat.zero sig)) (list_length (replicateLT r (famTypeC fam)))) (Nat.add (sigLength sig) (list_length (replicateLT r (famTypeC fam)))) (Nat.add (sigLength sig) r) (Eq.cong Nat Nat (fun (w : Nat) => Nat.add w (list_length (replicateLT r (famTypeC fam)))) (list_length (minorTys fam Nat.zero sig)) (sigLength sig) (minorTys_length fam Nat.zero sig)) (Eq.cong Nat Nat (fun (w : Nat) => Nat.add (sigLength sig) w) (list_length (replicateLT r (famTypeC fam))) r (replicateLT_length r (famTypeC fam)))))))))))) e e2 h",
            "GenRecContract fam sig u lhs rhs -> genSteps fam sig u lhs rhs — every object-level generic-recursor iota rule is realized as a real iota+β multi-step reduction. Generalizes natRecContract_steps to the SIGNATURE SCHEMA. GenRecContract.rec single `rule` case: head iota (iota_fires_gen) + β-telescope (lamTel_beta transported through genRecRhs_eq_lamTel/apply_spine_append + CRUX genRecRhs_instIter), hlen via list_append_length/minorTys_length/replicateLT_length/nat_succ_add, hj bridged listGet->lget. THE generic computation-fidelity theorem. SnSchema B4c COMPLETE.",
        )?;

        // ════════════════════════════════════════════════════════════════════
        // B6 §12 SN/ADEQUACY LADDER (foundation). genRecContract_steps above is
        // the first B6 rung. The ladder's accessibility engine (GenMajor) inducts
        // over the constructor-generated major class, whose `canon` case needs
        // list MEMBERSHIP (MemL) over the multi-field ctor spine, and whose `stuck`
        // case needs the iota-gate predicate GenStuckMajor. These structural pieces
        // are step-relation-independent, zero-axiom, census-neutral.
        // ════════════════════════════════════════════════════════════════════

        // MemL x xs: x occurs in the list xs (head or in the tail). The
        // multi-field member discipline of GenMajor.canon (what lets sig=[0,2]
        // binary trees work where the Nat [0,1] IsNumeral could not). Type-valued
        // (matches IsNumeral / genSteps) so its eliminations can build Type data.
        self.add_inductive(
            "inductive MemL : KExpr -> ListType KExpr -> Type\n| head : forall (x : KExpr) (rest : ListType KExpr), MemL x (ListType.cons KExpr x rest)\n| tail : forall (x : KExpr) (y : KExpr) (rest : ListType KExpr), MemL x rest -> MemL x (ListType.cons KExpr y rest)",
            "MemL x xs: membership of x in the list xs (head / tail closure). The member discipline of GenMajor.canon over a multi-field ctor spine. SnSchema B6 §12a'.",
        )?;
        // listGet_memL: a positive index lookup exhibits membership. ListType.rec on
        // xs, Nat.rec on the index; nil absurd (option_none_ne_some), cons/0 the head
        // (option_some_inj + substType to move the found element into MemL's slot),
        // cons/succ recurse (MemL.tail + lget_cons_succ-style defeq peel via listGet).
        self.add_recursive_def(
            "def listGet_memL (ms : ListType KExpr) : forall (j : Nat) (x : KExpr), Eq (OptionType KExpr) (listGet ms j) (OptionType.some KExpr x) -> MemL x ms := ListType.rec KExpr (fun (l : ListType KExpr) => forall (j : Nat) (x : KExpr), Eq (OptionType KExpr) (listGet l j) (OptionType.some KExpr x) -> MemL x l) (fun (j : Nat) (x : KExpr) (h : Eq (OptionType KExpr) (listGet (ListType.nil KExpr) j) (OptionType.some KExpr x)) => Eq.substType (OptionType KExpr) (fun (o : OptionType KExpr) => OptionType.rec KExpr (fun (_ : OptionType KExpr) => Type) Nat (fun (v : KExpr) => MemL x (ListType.nil KExpr)) o) (OptionType.none KExpr) (OptionType.some KExpr x) h Nat.zero) (fun (a : KExpr) (rest : ListType KExpr) (ih : forall (j : Nat) (x : KExpr), Eq (OptionType KExpr) (listGet rest j) (OptionType.some KExpr x) -> MemL x rest) => fun (j : Nat) => Nat.rec (fun (jj : Nat) => forall (x : KExpr), Eq (OptionType KExpr) (listGet (ListType.cons KExpr a rest) jj) (OptionType.some KExpr x) -> MemL x (ListType.cons KExpr a rest)) (fun (x : KExpr) (h : Eq (OptionType KExpr) (listGet (ListType.cons KExpr a rest) Nat.zero) (OptionType.some KExpr x)) => Eq.substType KExpr (fun (w : KExpr) => MemL w (ListType.cons KExpr a rest)) a x (option_some_inj KExpr a x h) (MemL.head a rest)) (fun (j0 : Nat) (_ : forall (x : KExpr), Eq (OptionType KExpr) (listGet (ListType.cons KExpr a rest) j0) (OptionType.some KExpr x) -> MemL x (ListType.cons KExpr a rest)) => fun (x : KExpr) (h : Eq (OptionType KExpr) (listGet (ListType.cons KExpr a rest) (Nat.succ j0)) (OptionType.some KExpr x)) => MemL.tail x a rest (ih j0 x h)) j) ms",
            "listGet ms j = some x -> MemL x ms (ListType.rec + Nat.rec; nil absurd, cons/0 head via option_some_inj+substType, cons/succ MemL.tail + ih). SnSchema B6 §12a'.",
        )?;
        // GenStuckMajor fam sig u t: t's head constant (if any) carries NO rule for
        // the generic recursor in genREnv — the gate under which the schematic iota
        // cannot fire on the full spine. The `stuck` case of GenMajor. Generalizes
        // the concrete StuckMajor.
        self.add_recursive_def(
            "def GenStuckMajor (fam : Name) (sig : ListType Nat) (u : Level) (t : KExpr) : Prop := forall (cn : Name), Eq (OptionType Name) (kexpr_const_name (kapp_fn t)) (OptionType.some Name cn) -> Eq (OptionType RecRule) (recrule_for (genREnv fam sig u) (genRecName fam sig) cn) (OptionType.none RecRule)",
            "GenStuckMajor fam sig u t: t's head const carries no genRec rule in genREnv (iota-gate). The stuck-major gate of GenMajor. SnSchema B6 §12e.",
        )?;

        // ── B6 PAYOFF: the generic-recursor SN theorem. Every CLOSED well-typed
        // term over the generic const-typing env genTEnv (where the family, its
        // constructors, and the generic recursor are typed constants) is
        // whnf-accessible (strongly normalizing), modulo a CandModel over genTEnv.
        // A one-line specialization of the Tait fundamental theorem
        // whnf_terminates_well_typed_dependent — EXACTLY mirroring the concrete
        // whnf_terminates_well_typed_nat (natrec.rs). The recursor's SN comes from
        // the typed-constant path (fundamental_const + fundamental_app), and its
        // iota head-expansion adequacy is the CandModel's generic redRecGen field
        // (B5). THE generic signature-schema recursor SN theorem — CandModel-
        // conditional (Gödel floor), zero domain axioms.
        self.add_recursive_def(
            "def whnf_terminates_well_typed_gen (fam : Name) (sig : ListType Nat) (u : Level) (M : CandModel (genTEnv fam sig u)) (e : KExpr) (T : KExpr) (h : TypingCtx (genTEnv fam sig u) (ListType.nil KExpr) e T) : whnf_acc e := whnf_terminates_well_typed_dependent (genTEnv fam sig u) M e T h",
            "whnf_terminates_well_typed_gen: every closed well-typed term over genTEnv (family/ctors/generic-recursor as typed consts) is whnf_acc (SN), modulo M : CandModel (genTEnv fam sig u). One-line specialization of whnf_terminates_well_typed_dependent, mirroring whnf_terminates_well_typed_nat. THE generic signature-schema recursor SN theorem. SnSchema B6 COMPLETE.",
        )?;

        // ── B7 PAYOFF: the INDEXED-family recursor SN theorem. Every closed
        // well-typed term over the indexed const-typing env iTEnv (the indexed
        // family, its constructors typed at their target indices, and the indexed
        // recursor, all typed constants) is whnf_acc (SN), modulo a CandModel over
        // iTEnv. One-line specialization of whnf_terminates_well_typed_dependent,
        // mirroring whnf_terminates_well_typed_gen/nat. Covers indexed inductive
        // families (Vec, and — instantiating at iFam=Nat, fam=Lt, nIdx=2, isig=sigLt
        // — the foundation's own Nat.lt/Le/Eq, which the base Nat.rec rung provably
        // cannot reach). THE fragment ladder's top-rung SN theorem — CandModel-
        // conditional (Gödel floor), zero domain axioms.
        self.add_recursive_def(
            "def whnf_terminates_well_typed_idx (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) (M : CandModel (iTEnv iFam fam nIdx isig u)) (e : KExpr) (T : KExpr) (h : TypingCtx (iTEnv iFam fam nIdx isig u) (ListType.nil KExpr) e T) : whnf_acc e := whnf_terminates_well_typed_dependent (iTEnv iFam fam nIdx isig u) M e T h",
            "whnf_terminates_well_typed_idx: every closed well-typed term over iTEnv (indexed family/ctors-at-target-indices/indexed-recursor as typed consts) is whnf_acc (SN), modulo M : CandModel (iTEnv ...). One-line specialization of whnf_terminates_well_typed_dependent, mirroring whnf_terminates_well_typed_gen. THE indexed-family recursor SN theorem — fragment ladder top rung. SnSchema B7 COMPLETE.",
        )?;

        // ── INDEXED ADEQUACY: env-OK tower + freshness + spine SN ──────────
        //
        // These live in the LATE add_snschema (not the objects stage) because
        // they consume name_eqb_refl (:864), nat_eqb_self_add_succ_false (:908)
        // and natFresh_red (natrec.rs, stage 79) — all registered AFTER
        // add_dependent_sn_richmodel. Same constraint the mutual lane's
        // mutREnv_ok tower has. Mirrors the genREnv_ok tower directly above.
        self.add_recursive_def(
            "def iREnv_meta_rec (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) : Eq (OptionType RecMeta) (recmeta_for (iREnv iFam fam nIdx isig u) (iRecName fam isig)) (OptionType.some RecMeta (iRecMeta nIdx isig)) := Eq.substType Bool (fun (b : Bool) => Eq (OptionType RecMeta) (opt_pick RecMeta b (iRecMeta nIdx isig) (OptionType.none RecMeta)) (OptionType.some RecMeta (iRecMeta nIdx isig))) Bool.true (name_eqb (iRecName fam isig) (iRecName fam isig)) (Eq.symm Bool (name_eqb (iRecName fam isig) (iRecName fam isig)) Bool.true (name_eqb_refl (iRecName fam isig))) (Eq.refl (OptionType RecMeta) (OptionType.some RecMeta (iRecMeta nIdx isig)))",
            "iREnv_meta_rec: recmeta_for (iREnv ...) (iRecName fam isig) = some (iRecMeta nIdx isig), via name_eqb_refl through the opt_pick. The indexed analogue of genREnv_meta_rec. Indexed adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def iRecRulesFrom_lookup (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) (j0 : Nat) (rest : ListType ICtor) (j : Nat) (dd : ICtor) (hjd : Eq (OptionType ICtor) (isigGet rest j) (OptionType.some ICtor dd)) : Eq (OptionType RecRule) (recrule_in_rules (iRecRulesFrom iFam fam nIdx isig u j0 rest) (ctorName fam (Nat.add j0 j))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add j0 j)) (Nat.add (icP dd) (recsLen (icRecs dd))) (iRecRhs iFam fam nIdx isig u (Nat.add j0 j) dd))) := ListType.rec ICtor (fun (rst : ListType ICtor) => forall (jb : Nat) (jo : Nat) (dv : ICtor), Eq (OptionType ICtor) (isigGet rst jo) (OptionType.some ICtor dv) -> Eq (OptionType RecRule) (recrule_in_rules (iRecRulesFrom iFam fam nIdx isig u jb rst) (ctorName fam (Nat.add jb jo))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add jb jo)) (Nat.add (icP dv) (recsLen (icRecs dv))) (iRecRhs iFam fam nIdx isig u (Nat.add jb jo) dv)))) (fun (jb : Nat) (jo : Nat) (dv : ICtor) (hh : Eq (OptionType ICtor) (isigGet (ListType.nil ICtor) jo) (OptionType.some ICtor dv)) => option_none_ne_some ICtor dv (Eq (OptionType RecRule) (recrule_in_rules (iRecRulesFrom iFam fam nIdx isig u jb (ListType.nil ICtor)) (ctorName fam (Nat.add jb jo))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add jb jo)) (Nat.add (icP dv) (recsLen (icRecs dv))) (iRecRhs iFam fam nIdx isig u (Nat.add jb jo) dv)))) hh) (fun (dh : ICtor) (rt : ListType ICtor) (ih : forall (jb : Nat) (jo : Nat) (dv : ICtor), Eq (OptionType ICtor) (isigGet rt jo) (OptionType.some ICtor dv) -> Eq (OptionType RecRule) (recrule_in_rules (iRecRulesFrom iFam fam nIdx isig u jb rt) (ctorName fam (Nat.add jb jo))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add jb jo)) (Nat.add (icP dv) (recsLen (icRecs dv))) (iRecRhs iFam fam nIdx isig u (Nat.add jb jo) dv)))) => fun (jb : Nat) (jo : Nat) (dv : ICtor) (hh : Eq (OptionType ICtor) (isigGet (ListType.cons ICtor dh rt) jo) (OptionType.some ICtor dv)) => Nat.rec (fun (jj : Nat) => Eq (OptionType ICtor) (isigGet (ListType.cons ICtor dh rt) jj) (OptionType.some ICtor dv) -> Eq (OptionType RecRule) (recrule_in_rules (iRecRulesFrom iFam fam nIdx isig u jb (ListType.cons ICtor dh rt)) (ctorName fam (Nat.add jb jj))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add jb jj)) (Nat.add (icP dv) (recsLen (icRecs dv))) (iRecRhs iFam fam nIdx isig u (Nat.add jb jj) dv)))) (fun (hz : Eq (OptionType ICtor) (isigGet (ListType.cons ICtor dh rt) Nat.zero) (OptionType.some ICtor dv)) => Eq.substType Bool (fun (bb : Bool) => Eq (OptionType RecRule) (opt_pick RecRule bb (RecRule.mk (ctorName fam jb) (Nat.add (icP dh) (recsLen (icRecs dh))) (iRecRhs iFam fam nIdx isig u jb dh)) (recrule_in_rules (iRecRulesFrom iFam fam nIdx isig u (Nat.add jb (Nat.succ Nat.zero)) rt) (ctorName fam (Nat.add jb Nat.zero)))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add jb Nat.zero)) (Nat.add (icP dv) (recsLen (icRecs dv))) (iRecRhs iFam fam nIdx isig u (Nat.add jb Nat.zero) dv)))) Bool.true (name_eqb (ctorName fam jb) (ctorName fam (Nat.add jb Nat.zero))) (Eq.symm Bool (name_eqb (ctorName fam jb) (ctorName fam (Nat.add jb Nat.zero))) Bool.true (name_eqb_refl (ctorName fam jb))) (Eq.cong ICtor (OptionType RecRule) (fun (dw : ICtor) => OptionType.some RecRule (RecRule.mk (ctorName fam jb) (Nat.add (icP dw) (recsLen (icRecs dw))) (iRecRhs iFam fam nIdx isig u jb dw))) dh dv (option_some_inj ICtor dh dv hz))) (fun (jp : Nat) (ihj : Eq (OptionType ICtor) (isigGet (ListType.cons ICtor dh rt) jp) (OptionType.some ICtor dv) -> Eq (OptionType RecRule) (recrule_in_rules (iRecRulesFrom iFam fam nIdx isig u jb (ListType.cons ICtor dh rt)) (ctorName fam (Nat.add jb jp))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add jb jp)) (Nat.add (icP dv) (recsLen (icRecs dv))) (iRecRhs iFam fam nIdx isig u (Nat.add jb jp) dv)))) => fun (hs : Eq (OptionType ICtor) (isigGet (ListType.cons ICtor dh rt) (Nat.succ jp)) (OptionType.some ICtor dv)) => Eq.substType Bool (fun (bb : Bool) => Eq (OptionType RecRule) (opt_pick RecRule bb (RecRule.mk (ctorName fam jb) (Nat.add (icP dh) (recsLen (icRecs dh))) (iRecRhs iFam fam nIdx isig u jb dh)) (recrule_in_rules (iRecRulesFrom iFam fam nIdx isig u (Nat.add jb (Nat.succ Nat.zero)) rt) (ctorName fam (Nat.add jb (Nat.succ jp))))) (OptionType.some RecRule (RecRule.mk (ctorName fam (Nat.add jb (Nat.succ jp))) (Nat.add (icP dv) (recsLen (icRecs dv))) (iRecRhs iFam fam nIdx isig u (Nat.add jb (Nat.succ jp)) dv)))) Bool.false (name_eqb (ctorName fam jb) (ctorName fam (Nat.add jb (Nat.succ jp)))) (Eq.symm Bool (name_eqb (ctorName fam jb) (ctorName fam (Nat.add jb (Nat.succ jp)))) Bool.false (Eq.trans Bool (name_eqb (ctorName fam jb) (ctorName fam (Nat.add jb (Nat.succ jp)))) (Bool.and Bool.true (nat_eqb jb (Nat.add jb (Nat.succ jp)))) Bool.false (Eq.cong Bool Bool (fun (bp : Bool) => Bool.and bp (nat_eqb jb (Nat.add jb (Nat.succ jp)))) (name_eqb fam fam) Bool.true (name_eqb_refl fam)) (nat_eqb_self_add_succ_false jb jp))) (Eq.substType Nat (fun (w : Nat) => Eq (OptionType RecRule) (recrule_in_rules (iRecRulesFrom iFam fam nIdx isig u (Nat.add jb (Nat.succ Nat.zero)) rt) (ctorName fam w)) (OptionType.some RecRule (RecRule.mk (ctorName fam w) (Nat.add (icP dv) (recsLen (icRecs dv))) (iRecRhs iFam fam nIdx isig u w dv)))) (Nat.add (Nat.add jb (Nat.succ Nat.zero)) jp) (Nat.add jb (Nat.succ jp)) (nat_succ_add jb jp) (ih (Nat.add jb (Nat.succ Nat.zero)) jp dv hs))) jo hh) rest j0 j dd hjd",
            "iRecRulesFrom_lookup: recrule lookup in the indexed signature-built rule list, by ListType.rec over the remaining ctors with an inner Nat.rec offset split. The indexed analogue of genRecRulesFrom_lookup. Indexed adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def iRecRules_lookup (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) (j : Nat) (dd : ICtor) (hjd : Eq (OptionType ICtor) (isigGet isig j) (OptionType.some ICtor dd)) : Eq (OptionType RecRule) (recrule_for (iREnv iFam fam nIdx isig u) (iRecName fam isig) (ctorName fam j)) (OptionType.some RecRule (RecRule.mk (ctorName fam j) (Nat.add (icP dd) (recsLen (icRecs dd))) (iRecRhs iFam fam nIdx isig u j dd))) := Eq.substType Bool (fun (bb : Bool) => Eq (OptionType RecRule) (OptionType.rec RecRules (fun (_ : OptionType RecRules) => OptionType RecRule) (OptionType.none RecRule) (fun (rules : RecRules) => recrule_in_rules rules (ctorName fam j)) (opt_pick RecRules bb (iRecRules iFam fam nIdx isig u) (OptionType.none RecRules))) (OptionType.some RecRule (RecRule.mk (ctorName fam j) (Nat.add (icP dd) (recsLen (icRecs dd))) (iRecRhs iFam fam nIdx isig u j dd)))) Bool.true (name_eqb (iRecName fam isig) (iRecName fam isig)) (Eq.symm Bool (name_eqb (iRecName fam isig) (iRecName fam isig)) Bool.true (name_eqb_refl (iRecName fam isig))) (Eq.substType Nat (fun (w : Nat) => Eq (OptionType RecRule) (recrule_in_rules (iRecRulesFrom iFam fam nIdx isig u Nat.zero isig) (ctorName fam w)) (OptionType.some RecRule (RecRule.mk (ctorName fam w) (Nat.add (icP dd) (recsLen (icRecs dd))) (iRecRhs iFam fam nIdx isig u w dd)))) (Nat.add Nat.zero j) j (nat_zero_add j) (iRecRulesFrom_lookup iFam fam nIdx isig u Nat.zero isig j dd hjd))",
            "iRecRules_lookup: recrule_for (iREnv ...) (iRecName fam isig) (ctorName fam j) resolves to ctor j's rule, composing the meta lookup with iRecRulesFrom_lookup. Indexed adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def iREnv_ok (iFam : Name) (fam : Name) (nIdx : Nat) (isig : ListType ICtor) (u : Level) : IGenRecEnvOK iFam fam nIdx isig u (iREnv iFam fam nIdx isig u) := IGenRecEnvOK.mk iFam fam nIdx isig u (iREnv iFam fam nIdx isig u) (iREnv_meta_rec iFam fam nIdx isig u) (fun (j : Nat) (dd : ICtor) (hjd : Eq (OptionType ICtor) (isigGet isig j) (OptionType.some ICtor dd)) => iRecRules_lookup iFam fam nIdx isig u j dd hjd)",
            "iREnv_ok: IGenRecEnvOK iFam fam nIdx isig u (iREnv iFam fam nIdx isig u) -- the concrete env-OK witness for the indexed lane, assembled from the two lookups above. The indexed counterpart of genREnv_ok and mutREnv_ok. Indexed adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def natFresh_to_iGenFresh (denv : DefEnv) (hf : NatFresh denv) : IGenFresh natName isigNat denv := NatFresh.rec (fun (_ : NatFresh denv) => IGenFresh natName isigNat denv) (fun (h0 : Eq (OptionType KExpr) (defval_for denv natName) (OptionType.none KExpr)) (h1 : Eq (OptionType KExpr) (defval_for denv zeroName) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (defval_for denv succName) (OptionType.none KExpr)) (h3 : Eq (OptionType KExpr) (defval_for denv recName) (OptionType.none KExpr)) => IGenFresh.mk natName isigNat denv h0 (natFresh_ctor_field denv h1 h2) h3) hf",
            "natFresh_to_iGenFresh: Converts a NatFresh pack into an IGenFresh pack at the Nat re-encoding isigNat -- the bridge letting the indexed lane reuse the concrete Nat freshness witness. Indexed adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def iFresh_red : IGenFresh natName isigNat (red_def the_red_env) := natFresh_to_iGenFresh (red_def the_red_env) natFresh_red",
            "iFresh_red: IGenFresh natName isigNat (red_def the_red_env) -- indexed freshness at the REAL reduction env, via natFresh_to_iGenFresh. NOTE available only at the concrete Nat re-encoding, where the names are concrete constants; the abstract-isig statement is not provable, for the same reason mutFresh_red is not. Indexed adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def whnfAccAll_append (xs : ListType KExpr) (ys : ListType KExpr) (hx : WhnfAccAll xs) (hy : WhnfAccAll ys) : WhnfAccAll (list_append xs ys) := WhnfAccAll.rec (fun (l : ListType KExpr) (_ : WhnfAccAll l) => WhnfAccAll (list_append l ys)) hy (fun (x : KExpr) (rest : ListType KExpr) (hxa : whnf_acc x) (hr : WhnfAccAll rest) (ihr : WhnfAccAll (list_append rest ys)) => WhnfAccAll.cons x (list_append rest ys) hxa ihr) xs hx",
            "whnfAccAll_append: WhnfAccAll (list_append xs ys) from WhnfAccAll xs and WhnfAccAll ys -- list-SN closure under append, needed where a ctor spine splits into params and fields. Indexed adequacy Phase 2.",
        )?;
        Ok(())
    }
}

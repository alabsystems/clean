// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mutual-inductive schema rung (8th fragment increment): the generalization of
//! the SnSchema single-family signature schema to K MUTUALLY-defined families.
//! A mutual block is `msig : ListType FamSpec`, each `FamSpec` a family name +
//! its per-ctor recursive-arg family-index lists (which family each recursive
//! argument recurses into). The per-family recursors each abstract ALL K motives
//! and ALL minor blocks; recursive calls dispatch to the right family's
//! recursor.
//!
//! Ported from the Aristotle-PROVEN guide
//! `scratch/aristotle-harvest/r3-mutual-schema/.../MutualSchema.lean` (all four
//! targets — mutREnv_ok / mutual_iota_fires_gen / mutRecRhs_instIter /
//! mutual_recContract_steps — proven there) via the workflow-produced
//! `scratch/mutual-schema-port-draft.md`. Per no-masquerade each string is
//! kernel-checked against the live spec; the Lean proof is a strategy guide.
//!
//! This module registers the OBJECT LAYER in dependency order. Bricks M1
//! (FamSpec + accessors + block arithmetic + per-family recursor
//! names/consts/motives), M1a telescopes, M1b rule-rhs, M1c env and M4 K=1
//! degeneration bridges have ALL landed here, together with the gates
//! (FamNamesDistinct / MutFresh / MutRecEnvOK) and the SN specialization
//! whnf_terminates_well_typed_mut. SINCE LANDED (2026-07-28): mutREnv_ok and
//! its lookup tower, the MutFresh projections, the inert-spine SN chain, and
//! the CONDITIONAL canonical-major arm mut_adequacy (registered in
//! add_acc_wtype, stage 135, because its SN gate ctorApp_whnfAcc lives there).
//! STILL TO PORT: mutual_iota_fires_gen / mutRecRhs_instIter /
//! mutual_recContract_steps.
//!
//! SCOPE HONESTY: mut_adequacy is NOT a capstone like w_adequacy. It is a
//! conditional canonical-major arm -- it takes the contractum's reducibility as
//! a hypothesis and closes in one application of the projected field. There is
//! no MutMajor class and no stuck arm, because MutualAdequacy.lean defines
//! neither (it has ZERO *_stuck theorems). Reaching W-lane parity would be
//! original design work, not a port. Census stays PINNED at 11.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Mutual-schema rung, Brick M1: the FamSpec block element, its accessors,
    /// the block-arithmetic helpers (family/ctor counts, offsets, lookups), and
    /// the per-family recursor names/constants/motive types. Reuses only the
    /// existing SnSchema `famTypeC` + foundation Nat/Name/ListType/OptionType;
    /// registered after `add_snschema`/`add_univ_poly` (terminal lemma layer).
    /// Mutual-block OBJECT prefix: family specs, recursor spine/rules/env,
    /// the contract inductive, and the two gates (`MutFresh`, `MutRecEnvOK`).
    ///
    /// Split out of `add_mutual_schema` and moved AHEAD of
    /// `add_dependent_sn_richmodel` so a CandModel `redRecMut` field can
    /// reference `mutRecApp`/`MutFresh`/`MutRecEnvOK`/`MutRecContract` — the
    /// stage-ordering prerequisite for the mutual adequacy layer. Exactly the
    /// idiom already used by `add_natrec_objects`, `add_snschema_objects` and
    /// `add_acc_wtype_objects`.
    ///
    /// Dependency check (mechanical, over all registered spec strings): the
    /// maximum external stage consumed by this half is 76
    /// (`add_snschema_objects`: sigNat/sigLength/ctorName/genRecName/famTypeC/
    /// genMotiveTy/genRecMeta/bvarSeq/ctorApp/minorTy/genRecTy/genRecRhsBody/
    /// genRecRhs/genRecRules/genREnv/genRecApp/listGet/genContractum), plus
    /// stages 1/6/7/8/9. NOTHING here reaches add_snschema (132) or
    /// add_univ_poly (133) — the old docstring's claim that this module is
    /// registered after them was a PLACEMENT note, not a dependency.
    /// Census-NEUTRAL pure reorder: no declaration is added or removed.
    pub(super) fn add_mutual_schema_objects(&mut self) -> Result<(), SpecError> {
        // FamSpec: one family of a mutual block — name + per-ctor recursive-arg
        // family-index lists (the ICtor idiom: single-ctor inductive + .rec
        // accessors).
        self.add_inductive(
            "inductive FamSpec : Type\n| mk : forall (f : Name) (sig : ListType (ListType Nat)), FamSpec",
            "FamSpec: one family of a mutual block — name + per-ctor recursive-arg family-index lists (sig entry j = ctor j's rec-arg family indices). MutSchema M1.",
        )?;
        self.add_recursive_def(
            "def famSpecName (d : FamSpec) : Name := FamSpec.rec (fun (_ : FamSpec) => Name) (fun (f : Name) (sig : ListType (ListType Nat)) => f) d",
            "famSpecName d: the family name of a FamSpec (FamSpec.rec projection). MutSchema M1.",
        )?;
        self.add_recursive_def(
            "def famSpecSig (d : FamSpec) : ListType (ListType Nat) := FamSpec.rec (fun (_ : FamSpec) => ListType (ListType Nat)) (fun (f : Name) (sig : ListType (ListType Nat)) => sig) d",
            "famSpecSig d: the per-ctor rec-arg-family-index signature of a FamSpec (FamSpec.rec projection). MutSchema M1.",
        )?;
        // famCount / ctorCount: monomorphic lengths (spec has no polymorphic length).
        self.add_recursive_def(
            "def famCount (msig : ListType FamSpec) : Nat := ListType.rec FamSpec (fun (_ : ListType FamSpec) => Nat) Nat.zero (fun (d : FamSpec) (rest : ListType FamSpec) (ih : Nat) => Nat.succ ih) msig",
            "famCount msig: number of families K in a mutual block (monomorphic length over ListType FamSpec). MutSchema M1.",
        )?;
        self.add_recursive_def(
            "def ctorCount (sig : ListType (ListType Nat)) : Nat := ListType.rec (ListType Nat) (fun (_ : ListType (ListType Nat)) => Nat) Nat.zero (fun (rs : ListType Nat) (rest : ListType (ListType Nat)) (ih : Nat) => Nat.succ ih) sig",
            "ctorCount sig: number of constructors of one family (length of its signature). MutSchema M1.",
        )?;
        // famNameAt / famSigAt: indexed lookups (nil-case default covers all i;
        // cons-case dispatches i via inner Nat.rec — the sigGet idiom).
        self.add_recursive_def(
            "def famNameAt (msig : ListType FamSpec) (i : Nat) : Name := ListType.rec FamSpec (fun (_ : ListType FamSpec) => Nat -> Name) (fun (i0 : Nat) => Name.anonymous) (fun (fs : FamSpec) (rest : ListType FamSpec) (ih : Nat -> Name) => fun (i0 : Nat) => Nat.rec (fun (_ : Nat) => Name) (famSpecName fs) (fun (i1 : Nat) (_ : Name) => ih i1) i0) msig i",
            "famNameAt msig i: the name of family i (default Name.anonymous out of range). MutSchema M1.",
        )?;
        self.add_recursive_def(
            "def famSigAt (msig : ListType FamSpec) (i : Nat) : ListType (ListType Nat) := ListType.rec FamSpec (fun (_ : ListType FamSpec) => Nat -> ListType (ListType Nat)) (fun (i0 : Nat) => ListType.nil (ListType Nat)) (fun (fs : FamSpec) (rest : ListType FamSpec) (ih : Nat -> ListType (ListType Nat)) => fun (i0 : Nat) => Nat.rec (fun (_ : Nat) => ListType (ListType Nat)) (famSpecSig fs) (fun (i1 : Nat) (_ : ListType (ListType Nat)) => ih i1) i0) msig i",
            "famSigAt msig i: the signature of family i (default nil out of range). MutSchema M1.",
        )?;
        // specGet / ctorSpecAt: constructor-spec lookup (generalizes sigGet).
        self.add_recursive_def(
            "def specGet (sig : ListType (ListType Nat)) (j : Nat) : OptionType (ListType Nat) := ListType.rec (ListType Nat) (fun (_ : ListType (ListType Nat)) => Nat -> OptionType (ListType Nat)) (fun (j0 : Nat) => OptionType.none (ListType Nat)) (fun (rs : ListType Nat) (rest : ListType (ListType Nat)) (ih : Nat -> OptionType (ListType Nat)) => fun (j0 : Nat) => Nat.rec (fun (_ : Nat) => OptionType (ListType Nat)) (OptionType.some (ListType Nat) rs) (fun (j1 : Nat) (_ : OptionType (ListType Nat)) => ih j1) j0) sig j",
            "specGet sig j: constructor j's rec-arg spec (none iff out of range). Generalizes sigGet to ListType (ListType Nat). MutSchema M1.",
        )?;
        self.add_recursive_def(
            "def ctorSpecAt (msig : ListType FamSpec) (i : Nat) (j : Nat) : OptionType (ListType Nat) := specGet (famSigAt msig i) j",
            "ctorSpecAt msig i j: spec of ctor j of family i (none out of range, incl. i>=K). MutSchema M1.",
        )?;
        // mutNumMinors / mutOffset: global minor arithmetic.
        self.add_recursive_def(
            "def mutNumMinors (msig : ListType FamSpec) : Nat := ListType.rec FamSpec (fun (_ : ListType FamSpec) => Nat) Nat.zero (fun (fs : FamSpec) (rest : ListType FamSpec) (ih : Nat) => Nat.add (ctorCount (famSpecSig fs)) ih) msig",
            "mutNumMinors msig: total number of minors N = ctors of the whole block. MutSchema M1.",
        )?;
        self.add_recursive_def(
            "def mutOffset (msig : ListType FamSpec) (i : Nat) : Nat := ListType.rec FamSpec (fun (_ : ListType FamSpec) => Nat -> Nat) (fun (i0 : Nat) => Nat.zero) (fun (fs : FamSpec) (rest : ListType FamSpec) (ih : Nat -> Nat) => fun (i0 : Nat) => Nat.rec (fun (_ : Nat) => Nat) Nat.zero (fun (i1 : Nat) (_ : Nat) => Nat.add (ctorCount (famSpecSig fs)) (ih i1)) i0) msig i",
            "mutOffset msig i: sum of earlier families' ctor counts; ctor (i,j)'s global minor index is mutOffset msig i + j. MutSchema M1.",
        )?;
        // Per-family recursor name/const/motive.
        self.add_recursive_def(
            "def mutRecName (msig : ListType FamSpec) (i : Nat) : Name := Name.str (famNameAt msig i) (ctorCount (famSigAt msig i))",
            "mutRecName msig i: recursor name of family i (Name.str fam (#ctors)); at K=1 this IS genRecName. MutSchema M1.",
        )?;
        self.add_recursive_def(
            "def mutFamC (msig : ListType FamSpec) (i : Nat) : KExpr := famTypeC (famNameAt msig i)",
            "mutFamC msig i: the family-i type constant. MutSchema M1.",
        )?;
        self.add_recursive_def(
            "def mutRecC (msig : ListType FamSpec) (u : Level) (i : Nat) : KExpr := KExpr.const (mutRecName msig i) (ListType.cons Level u (ListType.nil Level))",
            "mutRecC msig u i: the family-i recursor constant carrying its motive-universe level param. MutSchema M1.",
        )?;
        self.add_recursive_def(
            "def mutMotiveTy (msig : ListType FamSpec) (u : Level) (i : Nat) : KExpr := KExpr.pi (mutFamC msig i) (KExpr.sort u)",
            "mutMotiveTy msig u i: the family-i motive type fam_i -> Sort u. MutSchema M1.",
        )?;

        // ── §M1a: the joint telescopes. motivesPi/Lam abstract ALL K motives;
        // fieldsPi/Lam a ctor's fields (field p's domain is the fam it recurses
        // into); mutIhTel the per-field IH pack (motive C_fi at cbase+(K-1-fi));
        // mutMinorTy the mutual minor type for ctor (i,j) at global position g;
        // mutMinorsPi/Lam[Sig] the Π/λ over one family's / the whole block's
        // minors (threaded i,g,j counters); mutRecTy the family-i recursor type.
        self.add_recursive_def(
            "def motivesPi (u : Level) (msig : ListType FamSpec) (body : KExpr) : KExpr := ListType.rec FamSpec (fun (_ : ListType FamSpec) => KExpr) body (fun (fs : FamSpec) (rest : ListType FamSpec) (ih : KExpr) => KExpr.pi (KExpr.pi (famTypeC (famSpecName fs)) (KExpr.sort u)) ih) msig",
            "motivesPi u msig body: Pi over all K motives (family order, C_0 outermost). MutSchema M1a.",
        )?;
        self.add_recursive_def(
            "def motivesLam (u : Level) (msig : ListType FamSpec) (body : KExpr) : KExpr := ListType.rec FamSpec (fun (_ : ListType FamSpec) => KExpr) body (fun (fs : FamSpec) (rest : ListType FamSpec) (ih : KExpr) => KExpr.lam (KExpr.pi (famTypeC (famSpecName fs)) (KExpr.sort u)) ih) msig",
            "motivesLam u msig body: lambda over all K motives. MutSchema M1a.",
        )?;
        self.add_recursive_def(
            "def fieldsPi (msig : ListType FamSpec) (rs : ListType Nat) (body : KExpr) : KExpr := ListType.rec Nat (fun (_ : ListType Nat) => KExpr) body (fun (fi : Nat) (rest : ListType Nat) (ih : KExpr) => KExpr.pi (famTypeC (famNameAt msig fi)) ih) rs",
            "fieldsPi msig rs body: Pi over a ctor's fields (field p's domain = the family it recurses into). MutSchema M1a.",
        )?;
        self.add_recursive_def(
            "def fieldsLam (msig : ListType FamSpec) (rs : ListType Nat) (body : KExpr) : KExpr := ListType.rec Nat (fun (_ : ListType Nat) => KExpr) body (fun (fi : Nat) (rest : ListType Nat) (ih : KExpr) => KExpr.lam (famTypeC (famNameAt msig fi)) ih) rs",
            "fieldsLam msig rs body: lambda over a ctor's fields. MutSchema M1a.",
        )?;
        self.add_recursive_def(
            "def mutIhTel (K : Nat) (r : Nat) (cbase : Nat) (rs : ListType Nat) (body : KExpr) : KExpr := ListType.rec Nat (fun (_ : ListType Nat) => Nat -> KExpr) (fun (cb : Nat) => body) (fun (fi : Nat) (rest : ListType Nat) (ih : Nat -> KExpr) => fun (cb : Nat) => KExpr.pi (KExpr.app (KExpr.bvar (Nat.add cb (Nat.sub (Nat.sub K (Nat.succ Nat.zero)) fi))) (KExpr.bvar (Nat.sub r (Nat.succ Nat.zero)))) (ih (Nat.add cb (Nat.succ Nat.zero)))) rs cbase",
            "mutIhTel K r cbase rs body: per-field IH telescope (motive C_fi at cbase+(K-1-fi) applied to the field bvar). MutSchema M1a.",
        )?;
        self.add_recursive_def(
            "def mutMinorTy (msig : ListType FamSpec) (i : Nat) (g : Nat) (j : Nat) (rs : ListType Nat) : KExpr := fieldsPi msig rs (mutIhTel (famCount msig) (sigLength rs) (Nat.add g (sigLength rs)) rs (KExpr.app (KExpr.bvar (Nat.add (Nat.add g (Nat.add (sigLength rs) (sigLength rs))) (Nat.sub (Nat.sub (famCount msig) (Nat.succ Nat.zero)) i))) (ctorApp (famNameAt msig i) j (bvarSeq (Nat.sub (Nat.add (sigLength rs) (sigLength rs)) (Nat.succ Nat.zero)) (sigLength rs)))))",
            "mutMinorTy msig i g j rs: the mutual minor type for ctor j of family i at global minor position g (fields -> IH-pack -> motive-i at (ctor j fields)). MutSchema M1a.",
        )?;
        self.add_recursive_def(
            "def mutMinorsPiSig (msig : ListType FamSpec) (i : Nat) (g : Nat) (j : Nat) (sig : ListType (ListType Nat)) (body : KExpr) : KExpr := ListType.rec (ListType Nat) (fun (_ : ListType (ListType Nat)) => Nat -> Nat -> KExpr) (fun (g0 : Nat) (j0 : Nat) => body) (fun (rs : ListType Nat) (rest : ListType (ListType Nat)) (ih : Nat -> Nat -> KExpr) => fun (g0 : Nat) (j0 : Nat) => KExpr.pi (mutMinorTy msig i g0 j0 rs) (ih (Nat.add g0 (Nat.succ Nat.zero)) (Nat.add j0 (Nat.succ Nat.zero)))) sig g j",
            "mutMinorsPiSig: Pi over one family's minors (g,j threaded). MutSchema M1a.",
        )?;
        self.add_recursive_def(
            "def mutMinorsPi (msig : ListType FamSpec) (i : Nat) (g : Nat) (fams : ListType FamSpec) (body : KExpr) : KExpr := ListType.rec FamSpec (fun (_ : ListType FamSpec) => Nat -> Nat -> KExpr) (fun (i0 : Nat) (g0 : Nat) => body) (fun (fs : FamSpec) (rest : ListType FamSpec) (ih : Nat -> Nat -> KExpr) => fun (i0 : Nat) (g0 : Nat) => mutMinorsPiSig msig i0 g0 Nat.zero (famSpecSig fs) (ih (Nat.add i0 (Nat.succ Nat.zero)) (Nat.add g0 (ctorCount (famSpecSig fs))))) fams i g",
            "mutMinorsPi: Pi over ALL the block's minors (i,g threaded; walks a fams suffix). MutSchema M1a.",
        )?;
        self.add_recursive_def(
            "def mutMinorsLamSig (msig : ListType FamSpec) (i : Nat) (g : Nat) (j : Nat) (sig : ListType (ListType Nat)) (body : KExpr) : KExpr := ListType.rec (ListType Nat) (fun (_ : ListType (ListType Nat)) => Nat -> Nat -> KExpr) (fun (g0 : Nat) (j0 : Nat) => body) (fun (rs : ListType Nat) (rest : ListType (ListType Nat)) (ih : Nat -> Nat -> KExpr) => fun (g0 : Nat) (j0 : Nat) => KExpr.lam (mutMinorTy msig i g0 j0 rs) (ih (Nat.add g0 (Nat.succ Nat.zero)) (Nat.add j0 (Nat.succ Nat.zero)))) sig g j",
            "mutMinorsLamSig: lambda over one family's minors. MutSchema M1a.",
        )?;
        self.add_recursive_def(
            "def mutMinorsLam (msig : ListType FamSpec) (i : Nat) (g : Nat) (fams : ListType FamSpec) (body : KExpr) : KExpr := ListType.rec FamSpec (fun (_ : ListType FamSpec) => Nat -> Nat -> KExpr) (fun (i0 : Nat) (g0 : Nat) => body) (fun (fs : FamSpec) (rest : ListType FamSpec) (ih : Nat -> Nat -> KExpr) => fun (i0 : Nat) (g0 : Nat) => mutMinorsLamSig msig i0 g0 Nat.zero (famSpecSig fs) (ih (Nat.add i0 (Nat.succ Nat.zero)) (Nat.add g0 (ctorCount (famSpecSig fs))))) fams i g",
            "mutMinorsLam: lambda over ALL the block's minors. MutSchema M1a.",
        )?;
        self.add_recursive_def(
            "def mutRecTy (msig : ListType FamSpec) (u : Level) (i : Nat) : KExpr := motivesPi u msig (mutMinorsPi msig Nat.zero Nat.zero msig (KExpr.pi (mutFamC msig i) (KExpr.app (KExpr.bvar (Nat.add (Nat.add (mutNumMinors msig) (Nat.sub (Nat.sub (famCount msig) (Nat.succ Nat.zero)) i)) (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))))",
            "mutRecTy msig u i: THE mutual dependent recursor type of family i (all K motives, all minors, then Pi major -> motive-i at the major). At K=1 degenerates to genRecTy. MutSchema M1a.",
        )?;

        // ── §M1b: the rule-rhs. mutRecCalls builds the per-field recursive-call
        // spines (each field fi's recursive result = mutRecC for family fi applied
        // to the shared motives+minors prefix + the field; xIdx descends the field
        // de Bruijn indices); mutRecRhsBody = minor_g applied to the fields and
        // those recursive results; mutRecRhs the full λC* λm* λfields. body.
        self.add_recursive_def(
            "def mutRecCalls (msig : ListType FamSpec) (u : Level) (top : Nat) (cnt : Nat) (rs : ListType Nat) (xIdx : Nat) : ListType KExpr := ListType.rec Nat (fun (_ : ListType Nat) => Nat -> ListType KExpr) (fun (x0 : Nat) => ListType.nil KExpr) (fun (fi : Nat) (rest : ListType Nat) (ih : Nat -> ListType KExpr) => fun (x0 : Nat) => ListType.cons KExpr (apply_spine (list_append (bvarSeq top cnt) (ListType.cons KExpr (KExpr.bvar x0) (ListType.nil KExpr))) (mutRecC msig u fi)) (ih (Nat.sub x0 (Nat.succ Nat.zero)))) rs xIdx",
            "mutRecCalls: per-field recursive-call spines (field fi -> mutRecC for family fi on the motives+minors prefix + the field bvar; xIdx descends). MutSchema M1b.",
        )?;
        self.add_recursive_def(
            "def mutRecRhsBody (msig : ListType FamSpec) (u : Level) (g : Nat) (rs : ListType Nat) : KExpr := apply_spine (list_append (bvarSeq (Nat.sub (sigLength rs) (Nat.succ Nat.zero)) (sigLength rs)) (mutRecCalls msig u (Nat.sub (Nat.add (Nat.add (sigLength rs) (mutNumMinors msig)) (famCount msig)) (Nat.succ Nat.zero)) (Nat.add (famCount msig) (mutNumMinors msig)) rs (Nat.sub (sigLength rs) (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.add (sigLength rs) (Nat.sub (Nat.sub (mutNumMinors msig) (Nat.succ Nat.zero)) g)))",
            "mutRecRhsBody: the rule-rhs body = minor_g applied to the fields and the dispatched recursive results. MutSchema M1b.",
        )?;
        self.add_recursive_def(
            "def mutRecRhs (msig : ListType FamSpec) (u : Level) (g : Nat) (rs : ListType Nat) : KExpr := motivesLam u msig (mutMinorsLam msig Nat.zero Nat.zero msig (fieldsLam msig rs (mutRecRhsBody msig u g rs)))",
            "mutRecRhs msig u g rs: the full rule-rhs lambda (lam over motives, minors, fields; body = mutRecRhsBody). MutSchema M1b.",
        )?;

        // ── §M1c: the recursor rules + environment + application + contractum.
        // mutRecRulesSig/Rules build one family's RecRules; mutRecMeta the shared
        // metadata (0 params, K motives, N minors, 0 indices, major-after-minors);
        // mutREnvFrom K-fold addRec (recurses on the count k, threads family i);
        // mutREnv the full RecEnv; mutRecApp a fully-applied recursor spine;
        // mutRecs the dispatched recursive results (FLAG-Z: 2-list zip via nested
        // ListType.rec — outer on rs returns ListType KExpr -> ListType KExpr, inner
        // on fields discards its own ih and calls the OUTER ih on the field tail);
        // mutContractum the mutual iota contractum.
        self.add_recursive_def(
            "def mutRecRulesSig (msig : ListType FamSpec) (u : Level) (f : Name) (g : Nat) (j : Nat) (sig : ListType (ListType Nat)) : RecRules := ListType.rec (ListType Nat) (fun (_ : ListType (ListType Nat)) => Nat -> Nat -> RecRules) (fun (g0 : Nat) (j0 : Nat) => RecRules.nil) (fun (rs : ListType Nat) (rest : ListType (ListType Nat)) (ih : Nat -> Nat -> RecRules) => fun (g0 : Nat) (j0 : Nat) => RecRules.cons (RecRule.mk (ctorName f j0) (sigLength rs) (mutRecRhs msig u g0 rs)) (ih (Nat.add g0 (Nat.succ Nat.zero)) (Nat.add j0 (Nat.succ Nat.zero)))) sig g j",
            "mutRecRulesSig: one family's recursor rules (f fixed; g,j threaded). MutSchema M1c.",
        )?;
        self.add_recursive_def(
            "def mutRecRules (msig : ListType FamSpec) (u : Level) (i : Nat) : RecRules := mutRecRulesSig msig u (famNameAt msig i) (mutOffset msig i) Nat.zero (famSigAt msig i)",
            "mutRecRules msig u i: family i's recursor rules. MutSchema M1c.",
        )?;
        self.add_recursive_def(
            "def mutRecMeta (msig : ListType FamSpec) : RecMeta := RecMeta.mk Nat.zero (famCount msig) (mutNumMinors msig) Nat.zero Bool.true",
            "mutRecMeta msig: shared recursor metadata (0 params, K motives, N minors, 0 indices, major-after-minors). MutSchema M1c.",
        )?;
        self.add_recursive_def(
            "def mutREnvFrom (msig : ListType FamSpec) (u : Level) (i : Nat) (k : Nat) : RecEnv := Nat.rec (fun (_ : Nat) => Nat -> RecEnv) (fun (i0 : Nat) => RecEnv.empty) (fun (k0 : Nat) (ih : Nat -> RecEnv) => fun (i0 : Nat) => RecEnv.addRec (ih (Nat.add i0 (Nat.succ Nat.zero))) (mutRecName msig i0) (mutRecMeta msig) (mutRecRules msig u i0)) k i",
            "mutREnvFrom msig u i k: K-fold addRec building the mutual RecEnv (recurses on count k, threads family i). MutSchema M1c.",
        )?;
        self.add_recursive_def(
            "def mutREnv (msig : ListType FamSpec) (u : Level) : RecEnv := mutREnvFrom msig u Nat.zero (famCount msig)",
            "mutREnv msig u: the mutual recursor environment (all K families' recursors). MutSchema M1c.",
        )?;
        self.add_recursive_def(
            "def mutRecApp (msig : ListType FamSpec) (u : Level) (i : Nat) (cs : ListType KExpr) (ms : ListType KExpr) (t : KExpr) : KExpr := apply_spine (list_append cs (list_append ms (ListType.cons KExpr t (ListType.nil KExpr)))) (mutRecC msig u i)",
            "mutRecApp msig u i cs ms t: a fully-applied family-i recursor spine (rec_i C* m* t). MutSchema M1c.",
        )?;
        self.add_recursive_def(
            "def mutRecs (msig : ListType FamSpec) (u : Level) (cs : ListType KExpr) (ms : ListType KExpr) (rs : ListType Nat) (fields : ListType KExpr) : ListType KExpr := ListType.rec Nat (fun (_ : ListType Nat) => ListType KExpr -> ListType KExpr) (fun (flds : ListType KExpr) => ListType.nil KExpr) (fun (fi : Nat) (rest : ListType Nat) (ih : ListType KExpr -> ListType KExpr) => fun (flds : ListType KExpr) => ListType.rec KExpr (fun (_ : ListType KExpr) => ListType KExpr) (ListType.nil KExpr) (fun (x : KExpr) (xs : ListType KExpr) (_ : ListType KExpr) => ListType.cons KExpr (mutRecApp msig u fi cs ms x) (ih xs)) flds) rs fields",
            "mutRecs msig u cs ms rs fields: the dispatched recursive results (field fi -> mutRecApp for family fi; FLAG-Z 2-list zip via nested ListType.rec using the OUTER ih). MutSchema M1c.",
        )?;
        self.add_recursive_def(
            "def mutContractum (msig : ListType FamSpec) (u : Level) (cs : ListType KExpr) (ms : ListType KExpr) (mj : KExpr) (rs : ListType Nat) (fields : ListType KExpr) : KExpr := apply_spine (list_append fields (mutRecs msig u cs ms rs fields)) mj",
            "mutContractum: the mutual iota contractum (minor mj applied to the fields and the dispatched recursive results). MutSchema M1c.",
        )?;
        // MutRecContract: the mutual iota computation rule (mirrors GenRecContract):
        // rec_i C* m* (ctor (i,j) fields) contracts to minor_(offset i + j) applied
        // to fields ++ dispatched-recursive-results, given the arity/lookup premises.
        self.add_inductive(
            "inductive MutRecContract (msig : ListType FamSpec) (u : Level) : KExpr -> KExpr -> Type\n| rule : forall (i : Nat) (j : Nat) (rs : ListType Nat) (mj : KExpr) (cs : ListType KExpr) (ms : ListType KExpr) (fields : ListType KExpr), Eq (OptionType (ListType Nat)) (ctorSpecAt msig i j) (OptionType.some (ListType Nat) rs) -> Eq Nat (list_length cs) (famCount msig) -> Eq Nat (list_length ms) (mutNumMinors msig) -> Eq (OptionType KExpr) (listGet ms (Nat.add (mutOffset msig i) j)) (OptionType.some KExpr mj) -> Eq Nat (list_length fields) (sigLength rs) -> MutRecContract msig u (mutRecApp msig u i cs ms (ctorApp (famNameAt msig i) j fields)) (mutContractum msig u cs ms mj rs fields)",
            "MutRecContract msig u lhs rhs: the mutual iota computation rule — family-i recursor on ctor (i,j) contracts to minor (offset i + j) applied to fields ++ dispatched recursive calls. Generalizes GenRecContract. MutSchema M1c.",
        )?;

        // ── §M4: K=1 DEGENERATION bridges. degFam packages the Nat-shaped single
        // family [FamSpec.mk fam [[], [0]]] (sig [0,1]); the 16 Eq.refl bridges
        // prove every mutual object at K=1 computes EXACTLY to its concrete genRec*
        // counterpart — the strongest correctness test (any de Bruijn slip fails
        // by rfl). Validates the whole mutual schema against the landed Nat.rec /
        // SnSchema layer.
        self.add_recursive_def(
            "def degFam (fam : Name) : ListType FamSpec := ListType.cons FamSpec (FamSpec.mk fam (ListType.cons (ListType Nat) (ListType.nil Nat) (ListType.cons (ListType Nat) (ListType.cons Nat Nat.zero (ListType.nil Nat)) (ListType.nil (ListType Nat))))) (ListType.nil FamSpec)",
            "degFam fam: the Nat-shaped 1-family block [FamSpec.mk fam [[], [0]]] (the mutual packaging of sig [0,1]). MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def famNameAt_deg (fam : Name) : Eq Name (famNameAt (degFam fam) Nat.zero) fam := Eq.refl Name fam",
            "rfl bridge: famNameAt (degFam fam) 0 = fam. MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def mutRecName_deg (fam : Name) : Eq Name (mutRecName (degFam fam) Nat.zero) (genRecName fam sigNat) := Eq.refl Name (genRecName fam sigNat)",
            "rfl bridge: mutRecName (degFam fam) 0 = genRecName fam sigNat (ctorCount [[],[0]] = 2). MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def mutRecMeta_deg (fam : Name) : Eq RecMeta (mutRecMeta (degFam fam)) (genRecMeta sigNat) := Eq.refl RecMeta (genRecMeta sigNat)",
            "rfl bridge: mutRecMeta (degFam fam) = genRecMeta sigNat (0/1/2/0/true). MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def mutFamC_deg (fam : Name) : Eq KExpr (mutFamC (degFam fam) Nat.zero) (famTypeC fam) := Eq.refl KExpr (famTypeC fam)",
            "rfl bridge: mutFamC (degFam fam) 0 = famTypeC fam. MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def mutMotiveTy_deg (fam : Name) (u : Level) : Eq KExpr (mutMotiveTy (degFam fam) u Nat.zero) (genMotiveTy fam u) := Eq.refl KExpr (genMotiveTy fam u)",
            "rfl bridge: mutMotiveTy (degFam fam) u 0 = genMotiveTy fam u. MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def mutMinorTy_deg_zero (fam : Name) : Eq KExpr (mutMinorTy (degFam fam) Nat.zero Nat.zero Nat.zero (ListType.nil Nat)) (minorTy fam Nat.zero Nat.zero) := Eq.refl KExpr (minorTy fam Nat.zero Nat.zero)",
            "rfl bridge: mutMinorTy (degFam fam) 0 0 0 [] = minorTy fam 0 0 (zero-arm). MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def mutMinorTy_deg_succ (fam : Name) : Eq KExpr (mutMinorTy (degFam fam) Nat.zero (Nat.succ Nat.zero) (Nat.succ Nat.zero) (ListType.cons Nat Nat.zero (ListType.nil Nat))) (minorTy fam (Nat.succ Nat.zero) (Nat.succ Nat.zero)) := Eq.refl KExpr (minorTy fam (Nat.succ Nat.zero) (Nat.succ Nat.zero))",
            "rfl bridge: mutMinorTy (degFam fam) 0 1 1 [0] = minorTy fam 1 1 (the mutual de Bruijn telescope validation). MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def mutRecTy_deg (fam : Name) (u : Level) : Eq KExpr (mutRecTy (degFam fam) u Nat.zero) (genRecTy fam sigNat u) := Eq.refl KExpr (genRecTy fam sigNat u)",
            "rfl bridge: mutRecTy (degFam fam) u 0 = genRecTy fam sigNat u. MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def mutRecRhsBody_deg_zero (fam : Name) (u : Level) : Eq KExpr (mutRecRhsBody (degFam fam) u Nat.zero (ListType.nil Nat)) (genRecRhsBody fam sigNat u Nat.zero Nat.zero) := Eq.refl KExpr (genRecRhsBody fam sigNat u Nat.zero Nat.zero)",
            "rfl bridge: mutRecRhsBody (degFam fam) u 0 [] = genRecRhsBody fam sigNat u 0 0. MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def mutRecRhsBody_deg_succ (fam : Name) (u : Level) : Eq KExpr (mutRecRhsBody (degFam fam) u (Nat.succ Nat.zero) (ListType.cons Nat Nat.zero (ListType.nil Nat))) (genRecRhsBody fam sigNat u (Nat.succ Nat.zero) (Nat.succ Nat.zero)) := Eq.refl KExpr (genRecRhsBody fam sigNat u (Nat.succ Nat.zero) (Nat.succ Nat.zero))",
            "rfl bridge: mutRecRhsBody (degFam fam) u 1 [0] = genRecRhsBody fam sigNat u 1 1 (the hardest de Bruijn body). MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def mutRecRhs_deg_zero (fam : Name) (u : Level) : Eq KExpr (mutRecRhs (degFam fam) u Nat.zero (ListType.nil Nat)) (genRecRhs fam sigNat u Nat.zero Nat.zero) := Eq.refl KExpr (genRecRhs fam sigNat u Nat.zero Nat.zero)",
            "rfl bridge: mutRecRhs (degFam fam) u 0 [] = genRecRhs fam sigNat u 0 0. MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def mutRecRhs_deg_succ (fam : Name) (u : Level) : Eq KExpr (mutRecRhs (degFam fam) u (Nat.succ Nat.zero) (ListType.cons Nat Nat.zero (ListType.nil Nat))) (genRecRhs fam sigNat u (Nat.succ Nat.zero) (Nat.succ Nat.zero)) := Eq.refl KExpr (genRecRhs fam sigNat u (Nat.succ Nat.zero) (Nat.succ Nat.zero))",
            "rfl bridge: mutRecRhs (degFam fam) u 1 [0] = genRecRhs fam sigNat u 1 1. MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def mutRecRules_deg (fam : Name) (u : Level) : Eq RecRules (mutRecRules (degFam fam) u Nat.zero) (genRecRules fam sigNat u) := Eq.refl RecRules (genRecRules fam sigNat u)",
            "rfl bridge: mutRecRules (degFam fam) u 0 = genRecRules fam sigNat u. MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def mutREnv_deg (fam : Name) (u : Level) : Eq RecEnv (mutREnv (degFam fam) u) (genREnv fam sigNat u) := Eq.refl RecEnv (genREnv fam sigNat u)",
            "rfl bridge: mutREnv (degFam fam) u = genREnv fam sigNat u (K-fold collapses to a single addRec). MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def mutRecApp_deg (fam : Name) (u : Level) (m : KExpr) (t : KExpr) (ms : ListType KExpr) : Eq KExpr (mutRecApp (degFam fam) u Nat.zero (ListType.cons KExpr m (ListType.nil KExpr)) ms t) (genRecApp fam sigNat u m ms t) := Eq.refl KExpr (genRecApp fam sigNat u m ms t)",
            "rfl bridge: mutRecApp (degFam fam) u 0 [m] ms t = genRecApp fam sigNat u m ms t. MutSchema M4.",
        )?;
        self.add_recursive_def(
            "def mutContractum_deg_succ (fam : Name) (u : Level) (m : KExpr) (mj : KExpr) (x : KExpr) (ms : ListType KExpr) : Eq KExpr (mutContractum (degFam fam) u (ListType.cons KExpr m (ListType.nil KExpr)) ms mj (ListType.cons Nat Nat.zero (ListType.nil Nat)) (ListType.cons KExpr x (ListType.nil KExpr))) (genContractum fam sigNat u m ms mj (ListType.cons KExpr x (ListType.nil KExpr))) := Eq.refl KExpr (genContractum fam sigNat u m ms mj (ListType.cons KExpr x (ListType.nil KExpr)))",
            "rfl bridge: mutContractum (degFam fam) u [m] ms mj [0] [x] = genContractum fam sigNat u m ms mj [x] (validates the mutRecs zip degenerates to mapLT genRecApp). MutSchema M4.",
        )?;

        // ── Wellformedness predicates (single-mk inductives bundling the
        // conjuncts as ->-premises — the GenFresh/GenRecEnvOK idiom). Type-valued.
        // FamNamesDistinct: the K family names are pairwise distinct. MutFresh: the
        // block's family/ctor/recursor names are all unbound in a DefEnv (delta
        // won't fire on them). MutRecEnvOK: a RecEnv correctly stores every
        // family's recursor metadata + every ctor's rule (the mutREnv_ok target's
        // conclusion shape).
        self.add_inductive(
            "inductive FamNamesDistinct (msig : ListType FamSpec) : Type\n| mk : (forall (i : Nat) (i2 : Nat), Lt i (famCount msig) -> Lt i2 (famCount msig) -> (Eq Nat i i2 -> Empty) -> Eq Bool (name_eqb (famNameAt msig i) (famNameAt msig i2)) Bool.false) -> FamNamesDistinct msig",
            "FamNamesDistinct msig: the K family names of a mutual block are pairwise distinct. MutSchema M1c.",
        )?;
        self.add_inductive(
            "inductive MutFresh (msig : ListType FamSpec) (denv : DefEnv) : Type\n| mk : (forall (i : Nat), Lt i (famCount msig) -> Eq (OptionType KExpr) (defval_for denv (famNameAt msig i)) (OptionType.none KExpr)) -> (forall (i : Nat) (j : Nat), Lt i (famCount msig) -> Lt j (ctorCount (famSigAt msig i)) -> Eq (OptionType KExpr) (defval_for denv (ctorName (famNameAt msig i) j)) (OptionType.none KExpr)) -> (forall (i : Nat), Lt i (famCount msig) -> Eq (OptionType KExpr) (defval_for denv (mutRecName msig i)) (OptionType.none KExpr)) -> MutFresh msig denv",
            "MutFresh msig denv: every family/ctor/recursor name of the block is unbound in denv (delta won't fire). MutSchema M1c.",
        )?;
        self.add_inductive(
            "inductive MutRecEnvOK (msig : ListType FamSpec) (u : Level) : RecEnv -> Type\n| mk : forall (renv : RecEnv), (forall (i : Nat), Lt i (famCount msig) -> Eq (OptionType RecMeta) (recmeta_for renv (mutRecName msig i)) (OptionType.some RecMeta (mutRecMeta msig))) -> (forall (i : Nat) (j : Nat) (rs : ListType Nat), Eq (OptionType (ListType Nat)) (ctorSpecAt msig i j) (OptionType.some (ListType Nat) rs) -> Eq (OptionType RecRule) (recrule_for renv (mutRecName msig i) (ctorName (famNameAt msig i) j)) (OptionType.some RecRule (RecRule.mk (ctorName (famNameAt msig i) j) (sigLength rs) (mutRecRhs msig u (Nat.add (mutOffset msig i) j) rs)))) -> MutRecEnvOK msig u renv",
            "MutRecEnvOK msig u renv: renv stores every family's recursor metadata (mutRecMeta) and every ctor (i,j)'s rule (name/arity/mutRecRhs). The mutREnv_ok conclusion shape. MutSchema M1c.",
        )?;

        Ok(())
    }

    pub(super) fn add_mutual_schema(&mut self) -> Result<(), SpecError> {
        // NOTE: this LATE half now holds only the CandModel-dependent tail.
        // Everything else moved to add_mutual_schema_objects (early stage,
        // ahead of add_dependent_sn_richmodel) so a redRecMut CandModel field
        // can reference mutRecApp / MutFresh / MutRecEnvOK / MutRecContract.
        // Same two-stage idiom as add_acc_wtype_objects and add_snschema_objects.
        // ── SN via the fundamental-theorem path (the same one-liner that landed
        // nat/gen/indexed): mutTEnv is the K-family const-typing env (each family
        // typed at Sort 1, each family's recursor at mutRecTy); the SN theorem is
        // whnf_terminates_well_typed_dependent specialized at mutTEnv, with the
        // CandModel M an assumed parameter (the labeled Gödel-floor hypothesis, no
        // new field). mutTEnvFrom folds over the K families threading the index.
        self.add_recursive_def(
            "def mutTEnvFrom (msig : ListType FamSpec) (u : Level) (i : Nat) (fams : ListType FamSpec) (n : Name) : OptionType KExpr := ListType.rec FamSpec (fun (_ : ListType FamSpec) => Nat -> OptionType KExpr) (fun (i0 : Nat) => OptionType.none KExpr) (fun (fs : FamSpec) (rest : ListType FamSpec) (ih : Nat -> OptionType KExpr) => fun (i0 : Nat) => opt_pick KExpr (name_eqb n (famNameAt msig i0)) (KExpr.sort (Level.succ Level.zero)) (opt_pick KExpr (name_eqb n (mutRecName msig i0)) (mutRecTy msig u i0) (ih (Nat.add i0 (Nat.succ Nat.zero))))) fams i",
            "mutTEnvFrom: the K-family typing dispatch (each family i -> Sort 1, each recursor i -> mutRecTy; folds over families threading the index). MutSchema SN.",
        )?;
        self.add_recursive_def(
            "def mutTEnv (msig : ListType FamSpec) (u : Level) (n : Name) : OptionType KExpr := mutTEnvFrom msig u Nat.zero msig n",
            "mutTEnv msig u: the mutual const-typing env (families at Sort 1, recursors at mutRecTy). Generalizes genTEnv/iTEnv to mutual blocks. MutSchema SN.",
        )?;
        self.add_recursive_def(
            "def whnf_terminates_well_typed_mut (msig : ListType FamSpec) (u : Level) (M : CandModel (mutTEnv msig u)) (e : KExpr) (T : KExpr) (h : TypingCtx (mutTEnv msig u) (ListType.nil KExpr) e T) : whnf_acc e := whnf_terminates_well_typed_dependent (mutTEnv msig u) M e T h",
            "whnf_terminates_well_typed_mut: every closed well-typed term over the mutual typing env (K families + their recursors as typed consts) is whnf_acc (SN), modulo M : CandModel (mutTEnv ...). One-line specialization of whnf_terminates_well_typed_dependent, mirroring whnf_terminates_well_typed_gen/idx/nat. THE mutual-inductive recursor SN theorem. MutSchema SN.",
        )?;

        // ── MUTUAL ADEQUACY: freshness projections, env-OK tower, spine SN ──
        //
        // Registered at the END of the LATE stage so every dependency precedes
        // them: the tower consumes name_eqb_refl / nat_eqb_refl /
        // nat_eqb_self_add_succ_false (add_snschema, stage 132) and the
        // NatTrichotomy / nat_lt_le_dichotomy arithmetic
        // (add_dependent_sn_richmodel, stage 78).
        //
        // HONESTY NOTE on the freshness witnesses. The obvious target
        // `mutFresh_red : MutFresh msig (red_def the_red_env)` — the direct
        // analogue of natFresh_red and wFresh_red — is NOT PROVABLE, and not
        // merely hard: it is FALSE. Those two are `rfl` only because natName /
        // wName / supName are CONCRETE `Name.str Name.anonymous <lit>`, so every
        // name_eqb in the 51-node reflected def-env computes to false. Here
        // famNameAt/ctorName/mutRecName are ABSTRACT in msig, so name_eqb is
        // stuck; and for an adversarial msig whose family name collides with one
        // of the 51 interned names the proposition is genuinely false. So the
        // lane discharges freshness at DefEnv.empty (mutFresh_empty) plus
        // explicit projections, rather than asserting something untrue. The
        // MutFresh gate in RedRecMut quantifies denv, and the spec's whnf_acc is
        // env-FIXED, so this is sound — but the gate is correspondingly weaker
        // than the W/Nat lanes', and that is recorded rather than glossed.
        self.add_recursive_def(
            "def mutFresh_empty (msig : ListType FamSpec) : MutFresh msig DefEnv.empty := MutFresh.mk msig DefEnv.empty (fun (i : Nat) (_hi : Lt i (famCount msig)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (i : Nat) (j : Nat) (_hi : Lt i (famCount msig)) (_hj : Lt j (ctorCount (famSigAt msig i))) => Eq.refl (OptionType KExpr) (OptionType.none KExpr)) (fun (i : Nat) (_hi : Lt i (famCount msig)) => Eq.refl (OptionType KExpr) (OptionType.none KExpr))",
            "mutFresh_empty: MutFresh msig DefEnv.empty -- freshness at the EMPTY def-env, three rfl witnesses. This is what the mutual lane uses in place of a `mutFresh_red` at the real reduction env, because that statement is FALSE for abstract msig (see the block comment above). The gate it discharges is correspondingly weaker than the W/Nat lanes'. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def mutFresh_fam (msig : ListType FamSpec) (denv : DefEnv) (h : MutFresh msig denv) : forall (i : Nat), Lt i (famCount msig) -> Eq (OptionType KExpr) (defval_for denv (famNameAt msig i)) (OptionType.none KExpr) := MutFresh.rec msig denv (fun (_ : MutFresh msig denv) => forall (i : Nat), Lt i (famCount msig) -> Eq (OptionType KExpr) (defval_for denv (famNameAt msig i)) (OptionType.none KExpr)) (fun (h0 : forall (i : Nat), Lt i (famCount msig) -> Eq (OptionType KExpr) (defval_for denv (famNameAt msig i)) (OptionType.none KExpr)) (_h1 : forall (i : Nat) (j : Nat), Lt i (famCount msig) -> Lt j (ctorCount (famSigAt msig i)) -> Eq (OptionType KExpr) (defval_for denv (ctorName (famNameAt msig i) j)) (OptionType.none KExpr)) (_h2 : forall (i : Nat), Lt i (famCount msig) -> Eq (OptionType KExpr) (defval_for denv (mutRecName msig i)) (OptionType.none KExpr)) => h0) h",
            "mutFresh_fam: Projects the family-name conjunct out of a MutFresh pack: for i < famCount msig, defval_for denv (famNameAt msig i) = none. Carries the Lt bound as an explicit hypothesis. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def mutFresh_ctor (msig : ListType FamSpec) (denv : DefEnv) (h : MutFresh msig denv) : forall (i : Nat) (j : Nat), Lt i (famCount msig) -> Lt j (ctorCount (famSigAt msig i)) -> Eq (OptionType KExpr) (defval_for denv (ctorName (famNameAt msig i) j)) (OptionType.none KExpr) := MutFresh.rec msig denv (fun (_ : MutFresh msig denv) => forall (i : Nat) (j : Nat), Lt i (famCount msig) -> Lt j (ctorCount (famSigAt msig i)) -> Eq (OptionType KExpr) (defval_for denv (ctorName (famNameAt msig i) j)) (OptionType.none KExpr)) (fun (_h0 : forall (i : Nat), Lt i (famCount msig) -> Eq (OptionType KExpr) (defval_for denv (famNameAt msig i)) (OptionType.none KExpr)) (h1 : forall (i : Nat) (j : Nat), Lt i (famCount msig) -> Lt j (ctorCount (famSigAt msig i)) -> Eq (OptionType KExpr) (defval_for denv (ctorName (famNameAt msig i) j)) (OptionType.none KExpr)) (_h2 : forall (i : Nat), Lt i (famCount msig) -> Eq (OptionType KExpr) (defval_for denv (mutRecName msig i)) (OptionType.none KExpr)) => h1) h",
            "mutFresh_ctor: Projects the constructor-name conjunct out of a MutFresh pack, under Lt j (ctorCount (famSigAt msig i)). MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def mutFresh_rec (msig : ListType FamSpec) (denv : DefEnv) (h : MutFresh msig denv) : forall (i : Nat), Lt i (famCount msig) -> Eq (OptionType KExpr) (defval_for denv (mutRecName msig i)) (OptionType.none KExpr) := MutFresh.rec msig denv (fun (_ : MutFresh msig denv) => forall (i : Nat), Lt i (famCount msig) -> Eq (OptionType KExpr) (defval_for denv (mutRecName msig i)) (OptionType.none KExpr)) (fun (_h0 : forall (i : Nat), Lt i (famCount msig) -> Eq (OptionType KExpr) (defval_for denv (famNameAt msig i)) (OptionType.none KExpr)) (_h1 : forall (i : Nat) (j : Nat), Lt i (famCount msig) -> Lt j (ctorCount (famSigAt msig i)) -> Eq (OptionType KExpr) (defval_for denv (ctorName (famNameAt msig i) j)) (OptionType.none KExpr)) (h2 : forall (i : Nat), Lt i (famCount msig) -> Eq (OptionType KExpr) (defval_for denv (mutRecName msig i)) (OptionType.none KExpr)) => h2) h",
            "mutFresh_rec: Projects the recursor-name conjunct out of a MutFresh pack: defval_for denv (mutRecName msig i) = none. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def famCount_deg (fam : Name) : Eq Nat (famCount (degFam fam)) (Nat.succ Nat.zero) := Eq.refl Nat (Nat.succ Nat.zero)",
            "famCount_deg: famCount (degFam fam) = 1 by rfl -- the single-family degeneration fixture. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def mutNumMinors_deg (fam : Name) : Eq Nat (mutNumMinors (degFam fam)) (Nat.succ (Nat.succ Nat.zero)) := Eq.refl Nat (Nat.succ (Nat.succ Nat.zero))",
            "mutNumMinors_deg: mutNumMinors (degFam fam) = 2 by rfl. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def mutOffset_deg (fam : Name) : Eq Nat (mutOffset (degFam fam) Nat.zero) Nat.zero := Eq.refl Nat Nat.zero",
            "mutOffset_deg: mutOffset (degFam fam) 0 = 0 by rfl. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def ctorSpecAt_deg_zero (fam : Name) : Eq (OptionType (ListType Nat)) (ctorSpecAt (degFam fam) Nat.zero Nat.zero) (OptionType.some (ListType Nat) (ListType.nil Nat)) := Eq.refl (OptionType (ListType Nat)) (OptionType.some (ListType Nat) (ListType.nil Nat))",
            "ctorSpecAt_deg_zero: ctorSpecAt (degFam fam) 0 0 = some nil by rfl -- degenerate ctor-spec lookup, zero case. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def ctorSpecAt_deg_succ (fam : Name) : Eq (OptionType (ListType Nat)) (ctorSpecAt (degFam fam) Nat.zero (Nat.succ Nat.zero)) (OptionType.some (ListType Nat) (ListType.cons Nat Nat.zero (ListType.nil Nat))) := Eq.refl (OptionType (ListType Nat)) (OptionType.some (ListType Nat) (ListType.cons Nat Nat.zero (ListType.nil Nat)))",
            "ctorSpecAt_deg_succ: ctorSpecAt (degFam fam) 0 1 = some (cons 0 nil) by rfl -- degenerate ctor-spec lookup, succ case. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def mutContractum_deg_zero (fam : Name) (u : Level) (m : KExpr) (mj : KExpr) (ms : ListType KExpr) : Eq KExpr (mutContractum (degFam fam) u (ListType.cons KExpr m (ListType.nil KExpr)) ms mj (ListType.nil Nat) (ListType.nil KExpr)) (genContractum fam sigNat u m ms mj (ListType.nil KExpr)) := Eq.refl KExpr (genContractum fam sigNat u m ms mj (ListType.nil KExpr))",
            "mutContractum_deg_zero: mutContractum at the degenerate single-family signature reduces to the generic genContractum shape -- the rfl bridge tying the mutual construction to the already-checked first-order one. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def inertHead_beta_pres (n : Name) (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) n) (OptionType.none RecMeta)) (e : KExpr) (e2 : KExpr) (C : Type) (hb : beta_reduces e e2) (hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name n)) (k : Eq (OptionType Name) (kexpr_const_name (kapp_fn e2)) (OptionType.some Name n) -> C) : C := beta_reduces.rec (fun (s : KExpr) (t : KExpr) (_ : beta_reduces s t) => Eq (OptionType Name) (kexpr_const_name (kapp_fn s)) (OptionType.some Name n) -> (Eq (OptionType Name) (kexpr_const_name (kapp_fn t)) (OptionType.some Name n) -> C) -> C) (fun (A0 : KExpr) (body : KExpr) (arg : KExpr) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app (KExpr.lam A0 body) arg))) (OptionType.some Name n)) (kk : Eq (OptionType Name) (kexpr_const_name (kapp_fn (instantiate body arg))) (OptionType.some Name n) -> C) => option_none_ne_some_type Name n C hh) (fun (g : KExpr) (g2 : KExpr) (x0 : KExpr) (_hs : beta_reduces g g2) (ih : Eq (OptionType Name) (kexpr_const_name (kapp_fn g)) (OptionType.some Name n) -> (Eq (OptionType Name) (kexpr_const_name (kapp_fn g2)) (OptionType.some Name n) -> C) -> C) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app g x0))) (OptionType.some Name n)) (kk : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app g2 x0))) (OptionType.some Name n) -> C) => ih hh kk) (fun (g : KExpr) (x0 : KExpr) (x1 : KExpr) (_hs : beta_reduces x0 x1) (ih : Eq (OptionType Name) (kexpr_const_name (kapp_fn x0)) (OptionType.some Name n) -> (Eq (OptionType Name) (kexpr_const_name (kapp_fn x1)) (OptionType.some Name n) -> C) -> C) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app g x0))) (OptionType.some Name n)) (kk : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app g x1))) (OptionType.some Name n) -> C) => kk hh) (fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (_hs : beta_reduces ty ty2) (ih : Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name n) -> (Eq (OptionType Name) (kexpr_const_name (kapp_fn ty2)) (OptionType.some Name n) -> C) -> C) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam ty body))) (OptionType.some Name n)) (kk : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam ty2 body))) (OptionType.some Name n) -> C) => option_none_ne_some_type Name n C hh) (fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) (ih : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name n) -> (Eq (OptionType Name) (kexpr_const_name (kapp_fn body2)) (OptionType.some Name n) -> C) -> C) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam ty body))) (OptionType.some Name n)) (kk : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam ty body2))) (OptionType.some Name n) -> C) => option_none_ne_some_type Name n C hh) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hs : beta_reduces dom dom2) (ih : Eq (OptionType Name) (kexpr_const_name (kapp_fn dom)) (OptionType.some Name n) -> (Eq (OptionType Name) (kexpr_const_name (kapp_fn dom2)) (OptionType.some Name n) -> C) -> C) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi dom body))) (OptionType.some Name n)) (kk : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi dom2 body))) (OptionType.some Name n) -> C) => option_none_ne_some_type Name n C hh) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) (ih : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name n) -> (Eq (OptionType Name) (kexpr_const_name (kapp_fn body2)) (OptionType.some Name n) -> C) -> C) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi dom body))) (OptionType.some Name n)) (kk : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi dom body2))) (OptionType.some Name n) -> C) => option_none_ne_some_type Name n C hh) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (_hs : beta_reduces dom dom2) (ih : Eq (OptionType Name) (kexpr_const_name (kapp_fn dom)) (OptionType.some Name n) -> (Eq (OptionType Name) (kexpr_const_name (kapp_fn dom2)) (OptionType.some Name n) -> C) -> C) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom body))) (OptionType.some Name n)) (kk : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom2 body))) (OptionType.some Name n) -> C) => option_none_ne_some_type Name n C hh) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) (ih : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name n) -> (Eq (OptionType Name) (kexpr_const_name (kapp_fn body2)) (OptionType.some Name n) -> C) -> C) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom body))) (OptionType.some Name n)) (kk : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom body2))) (OptionType.some Name n) -> C) => option_none_ne_some_type Name n C hh) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name n)) (kk : Eq (OptionType Name) (kexpr_const_name (kapp_fn (instantiate body val))) (OptionType.some Name n) -> C) => option_none_ne_some_type Name n C hh) (fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) (_hs : beta_reduces ty ty2) (ih : Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name n) -> (Eq (OptionType Name) (kexpr_const_name (kapp_fn ty2)) (OptionType.some Name n) -> C) -> C) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name n)) (kk : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty2 val body))) (OptionType.some Name n) -> C) => option_none_ne_some_type Name n C hh) (fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) (_hs : beta_reduces val val2) (ih : Eq (OptionType Name) (kexpr_const_name (kapp_fn val)) (OptionType.some Name n) -> (Eq (OptionType Name) (kexpr_const_name (kapp_fn val2)) (OptionType.some Name n) -> C) -> C) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name n)) (kk : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val2 body))) (OptionType.some Name n) -> C) => option_none_ne_some_type Name n C hh) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) (_hs : beta_reduces body body2) (ih : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name n) -> (Eq (OptionType Name) (kexpr_const_name (kapp_fn body2)) (OptionType.some Name n) -> C) -> C) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name n)) (kk : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body2))) (OptionType.some Name n) -> C) => option_none_ne_some_type Name n C hh) (fun (e0 : KExpr) (e02 : KExpr) (hio : iota_reduces e0 e02) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn e0)) (OptionType.some Name n)) (_kk : Eq (OptionType Name) (kexpr_const_name (kapp_fn e02)) (OptionType.some Name n) -> C) => iota_step_no_recmeta_absurd (red_rec the_red_env) e0 e02 n C hh hrec (iota_reduces_to_step e0 e02 hio)) (fun (ps : Name) (pin : Nat) (sub : KExpr) (sub2 : KExpr) (_hs : beta_reduces sub sub2) (ih : Eq (OptionType Name) (kexpr_const_name (kapp_fn sub)) (OptionType.some Name n) -> (Eq (OptionType Name) (kexpr_const_name (kapp_fn sub2)) (OptionType.some Name n) -> C) -> C) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj ps pin sub))) (OptionType.some Name n)) (kk : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj ps pin sub2))) (OptionType.some Name n) -> C) => option_none_ne_some_type Name n C hh) e e2 hb hhead k",
            "inertHead_beta_pres: A beta step of an inert-headed application spine preserves inertness of the head. 15-arm beta_reduces.rec; the substrate for the spine SN chain below. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def inertApp_step_inv (n : Name) (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) n) (OptionType.none KExpr)) (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) n) (OptionType.none RecMeta)) (sh : KExpr) (ar : KExpr) (e2 : KExpr) (C : Type) (hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn sh)) (OptionType.some Name n)) (hs : whnf_step (KExpr.app sh ar) e2) (kL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr e2 (KExpr.app h2 ar) -> C) (kR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr e2 (KExpr.app sh a2) -> C) : C := whnf_step.rec (KExpr.app sh ar) e2 (fun (_ : whnf_step (KExpr.app sh ar) e2) => C) (fun (hbr : beta_reduces (KExpr.app sh ar) e2) => beta_reduces.rec (fun (s : KExpr) (t : KExpr) (_ : beta_reduces s t) => Eq KExpr s (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr t (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr t (KExpr.app sh a2) -> C) -> C) (fun (A0 : KExpr) (body : KExpr) (arg : KExpr) (heq : Eq KExpr (KExpr.app (KExpr.lam A0 body) arg) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr (instantiate body arg) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr (instantiate body arg) (KExpr.app sh a2) -> C) => option_none_ne_some_type Name n C (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam A0 body))) (kexpr_const_name (kapp_fn sh)) (OptionType.some Name n) (Eq.cong KExpr (OptionType Name) (fun (w : KExpr) => kexpr_const_name (kapp_fn w)) (KExpr.lam A0 body) sh (app_inj_fst (KExpr.lam A0 body) arg sh ar heq)) hhead)) (fun (g : KExpr) (g2 : KExpr) (x0 : KExpr) (hstp : beta_reduces g g2) (_ih : Eq KExpr g (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr g2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr g2 (KExpr.app sh a2) -> C) -> C) (heq : Eq KExpr (KExpr.app g x0) (KExpr.app sh ar)) (kkL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr (KExpr.app g2 x0) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr (KExpr.app g2 x0) (KExpr.app sh a2) -> C) => kkL g2 (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w g2) g sh (app_inj_fst g x0 sh ar heq) hstp) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app g2 w) x0 ar (app_inj_snd g x0 sh ar heq))) (fun (g : KExpr) (x0 : KExpr) (x1 : KExpr) (hstp : beta_reduces x0 x1) (_ih : Eq KExpr x0 (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr x1 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr x1 (KExpr.app sh a2) -> C) -> C) (heq : Eq KExpr (KExpr.app g x0) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr (KExpr.app g x1) (KExpr.app h2 ar) -> C) (kkR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr (KExpr.app g x1) (KExpr.app sh a2) -> C) => kkR x1 (Eq.substType KExpr (fun (w : KExpr) => beta_reduces w x1) x0 ar (app_inj_snd g x0 sh ar heq) hstp) (Eq.cong KExpr KExpr (fun (w : KExpr) => KExpr.app w x1) g sh (app_inj_fst g x0 sh ar heq))) (fun (ty : KExpr) (ty2 : KExpr) (body : KExpr) (hstp : beta_reduces ty ty2) (_ih : Eq KExpr ty (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr ty2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr ty2 (KExpr.app sh a2) -> C) -> C) (heq : Eq KExpr (KExpr.lam ty body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr (KExpr.lam ty2 body) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr (KExpr.lam ty2 body) (KExpr.app sh a2) -> C) => lam_ne_app ty body sh ar C heq) (fun (ty : KExpr) (body : KExpr) (body2 : KExpr) (hstp : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr body2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr body2 (KExpr.app sh a2) -> C) -> C) (heq : Eq KExpr (KExpr.lam ty body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr (KExpr.lam ty body2) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr (KExpr.lam ty body2) (KExpr.app sh a2) -> C) => lam_ne_app ty body sh ar C heq) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (hstp : beta_reduces dom dom2) (_ih : Eq KExpr dom (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr dom2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr dom2 (KExpr.app sh a2) -> C) -> C) (heq : Eq KExpr (KExpr.pi dom body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr (KExpr.pi dom2 body) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr (KExpr.pi dom2 body) (KExpr.app sh a2) -> C) => pi_ne_app dom body sh ar C heq) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (hstp : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr body2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr body2 (KExpr.app sh a2) -> C) -> C) (heq : Eq KExpr (KExpr.pi dom body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr (KExpr.pi dom body2) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr (KExpr.pi dom body2) (KExpr.app sh a2) -> C) => pi_ne_app dom body sh ar C heq) (fun (dom : KExpr) (dom2 : KExpr) (body : KExpr) (hstp : beta_reduces dom dom2) (_ih : Eq KExpr dom (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr dom2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr dom2 (KExpr.app sh a2) -> C) -> C) (heq : Eq KExpr (KExpr.forall_ dom body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr (KExpr.forall_ dom2 body) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr (KExpr.forall_ dom2 body) (KExpr.app sh a2) -> C) => pi_ne_app dom body sh ar C heq) (fun (dom : KExpr) (body : KExpr) (body2 : KExpr) (hstp : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr body2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr body2 (KExpr.app sh a2) -> C) -> C) (heq : Eq KExpr (KExpr.forall_ dom body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr (KExpr.forall_ dom body2) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr (KExpr.forall_ dom body2) (KExpr.app sh a2) -> C) => pi_ne_app dom body sh ar C heq) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr (instantiate body val) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr (instantiate body val) (KExpr.app sh a2) -> C) => let_ne_app ty val body sh ar C heq) (fun (ty : KExpr) (ty2 : KExpr) (val : KExpr) (body : KExpr) (hstp : beta_reduces ty ty2) (_ih : Eq KExpr ty (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr ty2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr ty2 (KExpr.app sh a2) -> C) -> C) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr (KExpr.let_ ty2 val body) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr (KExpr.let_ ty2 val body) (KExpr.app sh a2) -> C) => let_ne_app ty val body sh ar C heq) (fun (ty : KExpr) (val : KExpr) (val2 : KExpr) (body : KExpr) (hstp : beta_reduces val val2) (_ih : Eq KExpr val (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr val2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr val2 (KExpr.app sh a2) -> C) -> C) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr (KExpr.let_ ty val2 body) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr (KExpr.let_ ty val2 body) (KExpr.app sh a2) -> C) => let_ne_app ty val body sh ar C heq) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (body2 : KExpr) (hstp : beta_reduces body body2) (_ih : Eq KExpr body (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr body2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr body2 (KExpr.app sh a2) -> C) -> C) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr (KExpr.let_ ty val body2) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr (KExpr.let_ ty val body2) (KExpr.app sh a2) -> C) => let_ne_app ty val body sh ar C heq) (fun (e0 : KExpr) (e02 : KExpr) (hio : iota_reduces e0 e02) (heq : Eq KExpr e0 (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr e02 (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr e02 (KExpr.app sh a2) -> C) => iota_step_no_recmeta_absurd (red_rec the_red_env) e0 e02 n C (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn e0)) (kexpr_const_name (kapp_fn (KExpr.app sh ar))) (OptionType.some Name n) (Eq.cong KExpr (OptionType Name) (fun (w : KExpr) => kexpr_const_name (kapp_fn w)) e0 (KExpr.app sh ar) heq) hhead) hrec (iota_reduces_to_step e0 e02 hio)) (fun (ps : Name) (pin : Nat) (sub : KExpr) (sub2 : KExpr) (hstp : beta_reduces sub sub2) (_ih : Eq KExpr sub (KExpr.app sh ar) -> (forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr sub2 (KExpr.app h2 ar) -> C) -> (forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr sub2 (KExpr.app sh a2) -> C) -> C) (heq : Eq KExpr (KExpr.proj ps pin sub) (KExpr.app sh ar)) (_kkL : forall (h2 : KExpr), beta_reduces sh h2 -> Eq KExpr (KExpr.proj ps pin sub2) (KExpr.app h2 ar) -> C) (_kkR : forall (a2 : KExpr), beta_reduces ar a2 -> Eq KExpr (KExpr.proj ps pin sub2) (KExpr.app sh a2) -> C) => proj_ne_app ps pin sub sh ar C heq) (KExpr.app sh ar) e2 hbr (Eq.refl KExpr (KExpr.app sh ar)) kL kR) (fun (hdr : delta_reduces (KExpr.app sh ar) e2) => option_none_ne_some_type KExpr e2 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct (red_def the_red_env) (KExpr.app sh ar)) (OptionType.some KExpr e2) (Eq.symm (OptionType KExpr) (delta_reduct (red_def the_red_env) (KExpr.app sh ar)) (OptionType.none KExpr) (delta_reduct_eq_none_of_defval_none (red_def the_red_env) (KExpr.app sh ar) n hhead hdef)) (delta_reduces_to_step (KExpr.app sh ar) e2 hdr))) hs",
            "inertApp_step_inv: CPS inversion: a whnf step of an inert-headed application is a step in the head or in the argument. Same shape as the W lane's supApp_step_inv. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def whnfAcc_inertApp (n : Name) (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) n) (OptionType.none KExpr)) (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) n) (OptionType.none RecMeta)) (sh : KExpr) (hsh : whnf_acc sh) (ar : KExpr) (har : whnf_acc ar) (hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn sh)) (OptionType.some Name n)) : whnf_acc (KExpr.app sh ar) := whnf_acc.rec (fun (sh0 : KExpr) (_ : whnf_acc sh0) => Eq (OptionType Name) (kexpr_const_name (kapp_fn sh0)) (OptionType.some Name n) -> forall (a0 : KExpr), whnf_acc a0 -> whnf_acc (KExpr.app sh0 a0)) (fun (sh0 : KExpr) (hsacc : forall (h2 : KExpr), whnf_step sh0 h2 -> whnf_acc h2) (ihH : forall (h2 : KExpr), whnf_step sh0 h2 -> Eq (OptionType Name) (kexpr_const_name (kapp_fn h2)) (OptionType.some Name n) -> forall (a0 : KExpr), whnf_acc a0 -> whnf_acc (KExpr.app h2 a0)) => fun (hd0 : Eq (OptionType Name) (kexpr_const_name (kapp_fn sh0)) (OptionType.some Name n)) (a0 : KExpr) (ha0 : whnf_acc a0) => whnf_acc.rec (fun (a1 : KExpr) (_ : whnf_acc a1) => whnf_acc (KExpr.app sh0 a1)) (fun (a1 : KExpr) (haacc : forall (a2 : KExpr), whnf_step a1 a2 -> whnf_acc a2) (ihA : forall (a2 : KExpr), whnf_step a1 a2 -> whnf_acc (KExpr.app sh0 a2)) => whnf_acc.intro (KExpr.app sh0 a1) (fun (e3 : KExpr) (hstep : whnf_step (KExpr.app sh0 a1) e3) => inertApp_step_inv n hdef hrec sh0 a1 e3 (whnf_acc e3) hd0 hstep (fun (h2 : KExpr) (hb : beta_reduces sh0 h2) (heq : Eq KExpr e3 (KExpr.app h2 a1)) => inertHead_beta_pres n hrec sh0 h2 (whnf_acc e3) hb hd0 (fun (hd2 : Eq (OptionType Name) (kexpr_const_name (kapp_fn h2)) (OptionType.some Name n)) => Eq.substType KExpr (fun (w : KExpr) => whnf_acc w) (KExpr.app h2 a1) e3 (Eq.symm KExpr e3 (KExpr.app h2 a1) heq) (ihH h2 (whnf_step.beta sh0 h2 hb) hd2 a1 (whnf_acc.intro a1 haacc)))) (fun (a2 : KExpr) (hb : beta_reduces a1 a2) (heq : Eq KExpr e3 (KExpr.app sh0 a2)) => Eq.substType KExpr (fun (w : KExpr) => whnf_acc w) (KExpr.app sh0 a2) e3 (Eq.symm KExpr e3 (KExpr.app sh0 a2) heq) (ihA a2 (whnf_step.beta a1 a2 hb))))) a0 ha0) sh hsh hhead ar har",
            "whnfAcc_inertApp: whnf_acc of an inert-headed application, given whnf_acc of both parts -- Acc induction via inertApp_step_inv. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def whnfAcc_inertSpine (n : Name) (hdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) n) (OptionType.none KExpr)) (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) n) (OptionType.none RecMeta)) (xs : ListType KExpr) (hxs : WhnfAccAll xs) : forall (sh : KExpr), Eq (OptionType Name) (kexpr_const_name (kapp_fn sh)) (OptionType.some Name n) -> whnf_acc sh -> whnf_acc (apply_spine xs sh) := WhnfAccAll.rec (fun (l : ListType KExpr) (_ : WhnfAccAll l) => forall (sh : KExpr), Eq (OptionType Name) (kexpr_const_name (kapp_fn sh)) (OptionType.some Name n) -> whnf_acc sh -> whnf_acc (apply_spine l sh)) (fun (sh : KExpr) (_hd : Eq (OptionType Name) (kexpr_const_name (kapp_fn sh)) (OptionType.some Name n)) (hacc : whnf_acc sh) => hacc) (fun (x : KExpr) (rest : ListType KExpr) (hx : whnf_acc x) (_hrest : WhnfAccAll rest) (ih : forall (sh : KExpr), Eq (OptionType Name) (kexpr_const_name (kapp_fn sh)) (OptionType.some Name n) -> whnf_acc sh -> whnf_acc (apply_spine rest sh)) => fun (sh : KExpr) (hd : Eq (OptionType Name) (kexpr_const_name (kapp_fn sh)) (OptionType.some Name n)) (hacc : whnf_acc sh) => ih (KExpr.app sh x) hd (whnfAcc_inertApp n hdef hrec sh hacc x hx hd)) xs hxs",
            "whnfAcc_inertSpine: whnf_acc of an arbitrary-length inert-headed spine, by ListType induction over the argument list on top of whnfAcc_inertApp. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def famNamesDistinct_fact (msig : ListType FamSpec) (h : FamNamesDistinct msig) : forall (ia : Nat) (ib2 : Nat), Lt ia (famCount msig) -> Lt ib2 (famCount msig) -> (Eq Nat ia ib2 -> Empty) -> Eq Bool (name_eqb (famNameAt msig ia) (famNameAt msig ib2)) Bool.false := FamNamesDistinct.rec msig (fun (_hp : FamNamesDistinct msig) => forall (ia : Nat) (ib2 : Nat), Lt ia (famCount msig) -> Lt ib2 (famCount msig) -> (Eq Nat ia ib2 -> Empty) -> Eq Bool (name_eqb (famNameAt msig ia) (famNameAt msig ib2)) Bool.false) (fun (hf : forall (ia : Nat) (ib2 : Nat), Lt ia (famCount msig) -> Lt ib2 (famCount msig) -> (Eq Nat ia ib2 -> Empty) -> Eq Bool (name_eqb (famNameAt msig ia) (famNameAt msig ib2)) Bool.false) => hf) h",
            "famNamesDistinct_fact: Extracts the pointwise name-inequality fact from a FamNamesDistinct pack, in the Eq Bool (name_eqb ...) Bool.false form the env lookups need. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def ctorSpecAt_lt (msig : ListType FamSpec) (j : Nat) (rs : ListType Nat) (i : Nat) (h : Eq (OptionType (ListType Nat)) (ctorSpecAt msig i j) (OptionType.some (ListType Nat) rs)) : Lt i (famCount msig) := ListType.rec FamSpec (fun (l : ListType FamSpec) => forall (i0 : Nat), Eq (OptionType (ListType Nat)) (ctorSpecAt l i0 j) (OptionType.some (ListType Nat) rs) -> Lt i0 (famCount l)) (fun (i0 : Nat) (h0 : Eq (OptionType (ListType Nat)) (ctorSpecAt (ListType.nil FamSpec) i0 j) (OptionType.some (ListType Nat) rs)) => option_none_ne_some_type (ListType Nat) rs (Lt i0 (famCount (ListType.nil FamSpec))) h0) (fun (fs : FamSpec) (rest : ListType FamSpec) (ih : forall (i0 : Nat), Eq (OptionType (ListType Nat)) (ctorSpecAt rest i0 j) (OptionType.some (ListType Nat) rs) -> Lt i0 (famCount rest)) => fun (i0 : Nat) => Nat.rec (fun (ii : Nat) => Eq (OptionType (ListType Nat)) (ctorSpecAt (ListType.cons FamSpec fs rest) ii j) (OptionType.some (ListType Nat) rs) -> Lt ii (famCount (ListType.cons FamSpec fs rest))) (fun (_hz : Eq (OptionType (ListType Nat)) (ctorSpecAt (ListType.cons FamSpec fs rest) Nat.zero j) (OptionType.some (ListType Nat) rs)) => Lt.zero_lt_succ (famCount rest)) (fun (i1 : Nat) (_ihi : Eq (OptionType (ListType Nat)) (ctorSpecAt (ListType.cons FamSpec fs rest) i1 j) (OptionType.some (ListType Nat) rs) -> Lt i1 (famCount (ListType.cons FamSpec fs rest))) => fun (hs : Eq (OptionType (ListType Nat)) (ctorSpecAt (ListType.cons FamSpec fs rest) (Nat.succ i1) j) (OptionType.some (ListType Nat) rs)) => Lt.succ_lt_succ i1 (famCount rest) (ih i1 hs)) i0) msig i h",
            "ctorSpecAt_lt: ctorSpecAt msig i j = some rs implies Lt j (ctorCount (famSigAt msig i)) -- the index bound the rule lookup needs. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def mutREnvFrom_meta_lookup (msig : ListType FamSpec) (u : Level) (hd : forall (ia : Nat) (ib2 : Nat), Lt ia (famCount msig) -> Lt ib2 (famCount msig) -> (Eq Nat ia ib2 -> Empty) -> Eq Bool (name_eqb (famNameAt msig ia) (famNameAt msig ib2)) Bool.false) (k : Nat) (i0 : Nat) (d : Nat) (hdk : Lt d k) (hlt : Lt (Nat.add i0 d) (famCount msig)) : Eq (OptionType RecMeta) (recmeta_for (mutREnvFrom msig u i0 k) (mutRecName msig (Nat.add i0 d))) (OptionType.some RecMeta (mutRecMeta msig)) := Nat.rec (fun (kk : Nat) => forall (ib : Nat) (dd : Nat), Lt dd kk -> Lt (Nat.add ib dd) (famCount msig) -> Eq (OptionType RecMeta) (recmeta_for (mutREnvFrom msig u ib kk) (mutRecName msig (Nat.add ib dd))) (OptionType.some RecMeta (mutRecMeta msig))) (fun (ib : Nat) (dd : Nat) (hz : Lt dd Nat.zero) (_h2 : Lt (Nat.add ib dd) (famCount msig)) => Empty.rec (fun (_e : Empty) => Eq (OptionType RecMeta) (recmeta_for (mutREnvFrom msig u ib Nat.zero) (mutRecName msig (Nat.add ib dd))) (OptionType.some RecMeta (mutRecMeta msig))) (lt_zero_empty dd hz)) (fun (k0 : Nat) (ihk : forall (ib : Nat) (dd : Nat), Lt dd k0 -> Lt (Nat.add ib dd) (famCount msig) -> Eq (OptionType RecMeta) (recmeta_for (mutREnvFrom msig u ib k0) (mutRecName msig (Nat.add ib dd))) (OptionType.some RecMeta (mutRecMeta msig))) => fun (ib : Nat) (dd : Nat) => Nat.rec (fun (ee : Nat) => Lt ee (Nat.succ k0) -> Lt (Nat.add ib ee) (famCount msig) -> Eq (OptionType RecMeta) (recmeta_for (mutREnvFrom msig u ib (Nat.succ k0)) (mutRecName msig (Nat.add ib ee))) (OptionType.some RecMeta (mutRecMeta msig))) (fun (_hz1 : Lt Nat.zero (Nat.succ k0)) (_hz2 : Lt (Nat.add ib Nat.zero) (famCount msig)) => Eq.substType Bool (fun (bb : Bool) => Eq (OptionType RecMeta) (opt_pick RecMeta bb (mutRecMeta msig) (recmeta_for (mutREnvFrom msig u (Nat.add ib (Nat.succ Nat.zero)) k0) (mutRecName msig ib))) (OptionType.some RecMeta (mutRecMeta msig))) Bool.true (name_eqb (mutRecName msig ib) (mutRecName msig ib)) (Eq.symm Bool (name_eqb (mutRecName msig ib) (mutRecName msig ib)) Bool.true (name_eqb_refl (mutRecName msig ib))) (Eq.refl (OptionType RecMeta) (OptionType.some RecMeta (mutRecMeta msig)))) (fun (d0 : Nat) (_ihd : Lt d0 (Nat.succ k0) -> Lt (Nat.add ib d0) (famCount msig) -> Eq (OptionType RecMeta) (recmeta_for (mutREnvFrom msig u ib (Nat.succ k0)) (mutRecName msig (Nat.add ib d0))) (OptionType.some RecMeta (mutRecMeta msig))) => fun (hs1 : Lt (Nat.succ d0) (Nat.succ k0)) (hs2 : Lt (Nat.add ib (Nat.succ d0)) (famCount msig)) => Eq.substType Bool (fun (bb : Bool) => Eq (OptionType RecMeta) (opt_pick RecMeta bb (mutRecMeta msig) (recmeta_for (mutREnvFrom msig u (Nat.add ib (Nat.succ Nat.zero)) k0) (mutRecName msig (Nat.add ib (Nat.succ d0))))) (OptionType.some RecMeta (mutRecMeta msig))) Bool.false (name_eqb (mutRecName msig ib) (mutRecName msig (Nat.add ib (Nat.succ d0)))) (Eq.symm Bool (name_eqb (mutRecName msig ib) (mutRecName msig (Nat.add ib (Nat.succ d0)))) Bool.false (Eq.trans Bool (name_eqb (mutRecName msig ib) (mutRecName msig (Nat.add ib (Nat.succ d0)))) (Bool.and Bool.false (nat_eqb (ctorCount (famSigAt msig ib)) (ctorCount (famSigAt msig (Nat.add ib (Nat.succ d0)))))) Bool.false (Eq.cong Bool Bool (fun (bp : Bool) => Bool.and bp (nat_eqb (ctorCount (famSigAt msig ib)) (ctorCount (famSigAt msig (Nat.add ib (Nat.succ d0)))))) (name_eqb (famNameAt msig ib) (famNameAt msig (Nat.add ib (Nat.succ d0)))) Bool.false (hd ib (Nat.add ib (Nat.succ d0)) (lt_trans ib (Nat.add ib (Nat.succ d0)) (famCount msig) (lt_add_succ_left ib d0) hs2) hs2 (nat_lt_ne ib (Nat.add ib (Nat.succ d0)) (lt_add_succ_left ib d0)))) (Eq.refl Bool Bool.false))) (Eq.substType Nat (fun (w : Nat) => Eq (OptionType RecMeta) (recmeta_for (mutREnvFrom msig u (Nat.add ib (Nat.succ Nat.zero)) k0) (mutRecName msig w)) (OptionType.some RecMeta (mutRecMeta msig))) (Nat.add (Nat.add ib (Nat.succ Nat.zero)) d0) (Nat.add ib (Nat.succ d0)) (nat_succ_add ib d0) (ihk (Nat.add ib (Nat.succ Nat.zero)) d0 (lt_succ_succ_to_lt d0 k0 hs1) (Eq.substType Nat (fun (w : Nat) => Lt w (famCount msig)) (Nat.add ib (Nat.succ d0)) (Nat.add (Nat.add ib (Nat.succ Nat.zero)) d0) (Eq.symm Nat (Nat.add (Nat.add ib (Nat.succ Nat.zero)) d0) (Nat.add ib (Nat.succ d0)) (nat_succ_add ib d0)) hs2)))) dd) k i0 d hdk hlt",
            "mutREnvFrom_meta_lookup: recmeta_for on the folded mutual env returns mutRecMeta for every family index in range. Nat.rec over the node count with the running index threaded through the motive; the multi-node generalization of genREnv_meta_rec, which only handles a single addRec node. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def mutREnvFrom_rules_lookup (msig : ListType FamSpec) (u : Level) (hd : forall (ia : Nat) (ib2 : Nat), Lt ia (famCount msig) -> Lt ib2 (famCount msig) -> (Eq Nat ia ib2 -> Empty) -> Eq Bool (name_eqb (famNameAt msig ia) (famNameAt msig ib2)) Bool.false) (k : Nat) (i0 : Nat) (d : Nat) (hdk : Lt d k) (hlt : Lt (Nat.add i0 d) (famCount msig)) : Eq (OptionType RecRules) (recrules_for (mutREnvFrom msig u i0 k) (mutRecName msig (Nat.add i0 d))) (OptionType.some RecRules (mutRecRules msig u (Nat.add i0 d))) := Nat.rec (fun (kk : Nat) => forall (ib : Nat) (dd : Nat), Lt dd kk -> Lt (Nat.add ib dd) (famCount msig) -> Eq (OptionType RecRules) (recrules_for (mutREnvFrom msig u ib kk) (mutRecName msig (Nat.add ib dd))) (OptionType.some RecRules (mutRecRules msig u (Nat.add ib dd)))) (fun (ib : Nat) (dd : Nat) (hz : Lt dd Nat.zero) (_h2 : Lt (Nat.add ib dd) (famCount msig)) => Empty.rec (fun (_e : Empty) => Eq (OptionType RecRules) (recrules_for (mutREnvFrom msig u ib Nat.zero) (mutRecName msig (Nat.add ib dd))) (OptionType.some RecRules (mutRecRules msig u (Nat.add ib dd)))) (lt_zero_empty dd hz)) (fun (k0 : Nat) (ihk : forall (ib : Nat) (dd : Nat), Lt dd k0 -> Lt (Nat.add ib dd) (famCount msig) -> Eq (OptionType RecRules) (recrules_for (mutREnvFrom msig u ib k0) (mutRecName msig (Nat.add ib dd))) (OptionType.some RecRules (mutRecRules msig u (Nat.add ib dd)))) => fun (ib : Nat) (dd : Nat) => Nat.rec (fun (ee : Nat) => Lt ee (Nat.succ k0) -> Lt (Nat.add ib ee) (famCount msig) -> Eq (OptionType RecRules) (recrules_for (mutREnvFrom msig u ib (Nat.succ k0)) (mutRecName msig (Nat.add ib ee))) (OptionType.some RecRules (mutRecRules msig u (Nat.add ib ee)))) (fun (_hz1 : Lt Nat.zero (Nat.succ k0)) (_hz2 : Lt (Nat.add ib Nat.zero) (famCount msig)) => Eq.substType Bool (fun (bb : Bool) => Eq (OptionType RecRules) (opt_pick RecRules bb (mutRecRules msig u ib) (recrules_for (mutREnvFrom msig u (Nat.add ib (Nat.succ Nat.zero)) k0) (mutRecName msig ib))) (OptionType.some RecRules (mutRecRules msig u ib))) Bool.true (name_eqb (mutRecName msig ib) (mutRecName msig ib)) (Eq.symm Bool (name_eqb (mutRecName msig ib) (mutRecName msig ib)) Bool.true (name_eqb_refl (mutRecName msig ib))) (Eq.refl (OptionType RecRules) (OptionType.some RecRules (mutRecRules msig u ib)))) (fun (d0 : Nat) (_ihd : Lt d0 (Nat.succ k0) -> Lt (Nat.add ib d0) (famCount msig) -> Eq (OptionType RecRules) (recrules_for (mutREnvFrom msig u ib (Nat.succ k0)) (mutRecName msig (Nat.add ib d0))) (OptionType.some RecRules (mutRecRules msig u (Nat.add ib d0)))) => fun (hs1 : Lt (Nat.succ d0) (Nat.succ k0)) (hs2 : Lt (Nat.add ib (Nat.succ d0)) (famCount msig)) => Eq.substType Bool (fun (bb : Bool) => Eq (OptionType RecRules) (opt_pick RecRules bb (mutRecRules msig u ib) (recrules_for (mutREnvFrom msig u (Nat.add ib (Nat.succ Nat.zero)) k0) (mutRecName msig (Nat.add ib (Nat.succ d0))))) (OptionType.some RecRules (mutRecRules msig u (Nat.add ib (Nat.succ d0))))) Bool.false (name_eqb (mutRecName msig ib) (mutRecName msig (Nat.add ib (Nat.succ d0)))) (Eq.symm Bool (name_eqb (mutRecName msig ib) (mutRecName msig (Nat.add ib (Nat.succ d0)))) Bool.false (Eq.trans Bool (name_eqb (mutRecName msig ib) (mutRecName msig (Nat.add ib (Nat.succ d0)))) (Bool.and Bool.false (nat_eqb (ctorCount (famSigAt msig ib)) (ctorCount (famSigAt msig (Nat.add ib (Nat.succ d0)))))) Bool.false (Eq.cong Bool Bool (fun (bp : Bool) => Bool.and bp (nat_eqb (ctorCount (famSigAt msig ib)) (ctorCount (famSigAt msig (Nat.add ib (Nat.succ d0)))))) (name_eqb (famNameAt msig ib) (famNameAt msig (Nat.add ib (Nat.succ d0)))) Bool.false (hd ib (Nat.add ib (Nat.succ d0)) (lt_trans ib (Nat.add ib (Nat.succ d0)) (famCount msig) (lt_add_succ_left ib d0) hs2) hs2 (nat_lt_ne ib (Nat.add ib (Nat.succ d0)) (lt_add_succ_left ib d0)))) (Eq.refl Bool Bool.false))) (Eq.substType Nat (fun (w : Nat) => Eq (OptionType RecRules) (recrules_for (mutREnvFrom msig u (Nat.add ib (Nat.succ Nat.zero)) k0) (mutRecName msig w)) (OptionType.some RecRules (mutRecRules msig u w))) (Nat.add (Nat.add ib (Nat.succ Nat.zero)) d0) (Nat.add ib (Nat.succ d0)) (nat_succ_add ib d0) (ihk (Nat.add ib (Nat.succ Nat.zero)) d0 (lt_succ_succ_to_lt d0 k0 hs1) (Eq.substType Nat (fun (w : Nat) => Lt w (famCount msig)) (Nat.add ib (Nat.succ d0)) (Nat.add (Nat.add ib (Nat.succ Nat.zero)) d0) (Eq.symm Nat (Nat.add (Nat.add ib (Nat.succ Nat.zero)) d0) (Nat.add ib (Nat.succ d0)) (nat_succ_add ib d0)) hs2)))) dd) k i0 d hdk hlt",
            "mutREnvFrom_rules_lookup: recrules_for on the folded mutual env returns the right family's rule list. Same induction shape as the meta lookup, at recrules_for. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def mutRecRulesSig_lookup (msig : ListType FamSpec) (u : Level) (f : Name) (sig : ListType (ListType Nat)) (g0 : Nat) (j0 : Nat) (j : Nat) (rs : ListType Nat) (h : Eq (OptionType (ListType Nat)) (specGet sig j) (OptionType.some (ListType Nat) rs)) : Eq (OptionType RecRule) (recrule_in_rules (mutRecRulesSig msig u f g0 j0 sig) (ctorName f (Nat.add j0 j))) (OptionType.some RecRule (RecRule.mk (ctorName f (Nat.add j0 j)) (sigLength rs) (mutRecRhs msig u (Nat.add g0 j) rs))) := ListType.rec (ListType Nat) (fun (sg : ListType (ListType Nat)) => forall (gb : Nat) (jb : Nat) (jo : Nat) (rv : ListType Nat), Eq (OptionType (ListType Nat)) (specGet sg jo) (OptionType.some (ListType Nat) rv) -> Eq (OptionType RecRule) (recrule_in_rules (mutRecRulesSig msig u f gb jb sg) (ctorName f (Nat.add jb jo))) (OptionType.some RecRule (RecRule.mk (ctorName f (Nat.add jb jo)) (sigLength rv) (mutRecRhs msig u (Nat.add gb jo) rv)))) (fun (gb : Nat) (jb : Nat) (jo : Nat) (rv : ListType Nat) (hh : Eq (OptionType (ListType Nat)) (specGet (ListType.nil (ListType Nat)) jo) (OptionType.some (ListType Nat) rv)) => option_none_ne_some (ListType Nat) rv (Eq (OptionType RecRule) (recrule_in_rules (mutRecRulesSig msig u f gb jb (ListType.nil (ListType Nat))) (ctorName f (Nat.add jb jo))) (OptionType.some RecRule (RecRule.mk (ctorName f (Nat.add jb jo)) (sigLength rv) (mutRecRhs msig u (Nat.add gb jo) rv)))) hh) (fun (rh : ListType Nat) (rt : ListType (ListType Nat)) (ih : forall (gb : Nat) (jb : Nat) (jo : Nat) (rv : ListType Nat), Eq (OptionType (ListType Nat)) (specGet rt jo) (OptionType.some (ListType Nat) rv) -> Eq (OptionType RecRule) (recrule_in_rules (mutRecRulesSig msig u f gb jb rt) (ctorName f (Nat.add jb jo))) (OptionType.some RecRule (RecRule.mk (ctorName f (Nat.add jb jo)) (sigLength rv) (mutRecRhs msig u (Nat.add gb jo) rv)))) => fun (gb : Nat) (jb : Nat) (jo : Nat) (rv : ListType Nat) (hh : Eq (OptionType (ListType Nat)) (specGet (ListType.cons (ListType Nat) rh rt) jo) (OptionType.some (ListType Nat) rv)) => Nat.rec (fun (jj : Nat) => Eq (OptionType (ListType Nat)) (specGet (ListType.cons (ListType Nat) rh rt) jj) (OptionType.some (ListType Nat) rv) -> Eq (OptionType RecRule) (recrule_in_rules (mutRecRulesSig msig u f gb jb (ListType.cons (ListType Nat) rh rt)) (ctorName f (Nat.add jb jj))) (OptionType.some RecRule (RecRule.mk (ctorName f (Nat.add jb jj)) (sigLength rv) (mutRecRhs msig u (Nat.add gb jj) rv)))) (fun (hz : Eq (OptionType (ListType Nat)) (specGet (ListType.cons (ListType Nat) rh rt) Nat.zero) (OptionType.some (ListType Nat) rv)) => Eq.substType Bool (fun (bb : Bool) => Eq (OptionType RecRule) (opt_pick RecRule bb (RecRule.mk (ctorName f jb) (sigLength rh) (mutRecRhs msig u gb rh)) (recrule_in_rules (mutRecRulesSig msig u f (Nat.add gb (Nat.succ Nat.zero)) (Nat.add jb (Nat.succ Nat.zero)) rt) (ctorName f (Nat.add jb Nat.zero)))) (OptionType.some RecRule (RecRule.mk (ctorName f (Nat.add jb Nat.zero)) (sigLength rv) (mutRecRhs msig u (Nat.add gb Nat.zero) rv)))) Bool.true (name_eqb (ctorName f jb) (ctorName f (Nat.add jb Nat.zero))) (Eq.symm Bool (name_eqb (ctorName f jb) (ctorName f (Nat.add jb Nat.zero))) Bool.true (name_eqb_refl (ctorName f jb))) (Eq.cong (ListType Nat) (OptionType RecRule) (fun (w : ListType Nat) => OptionType.some RecRule (RecRule.mk (ctorName f jb) (sigLength w) (mutRecRhs msig u gb w))) rh rv (option_some_inj (ListType Nat) rh rv hz))) (fun (jp : Nat) (_ihj : Eq (OptionType (ListType Nat)) (specGet (ListType.cons (ListType Nat) rh rt) jp) (OptionType.some (ListType Nat) rv) -> Eq (OptionType RecRule) (recrule_in_rules (mutRecRulesSig msig u f gb jb (ListType.cons (ListType Nat) rh rt)) (ctorName f (Nat.add jb jp))) (OptionType.some RecRule (RecRule.mk (ctorName f (Nat.add jb jp)) (sigLength rv) (mutRecRhs msig u (Nat.add gb jp) rv)))) => fun (hs : Eq (OptionType (ListType Nat)) (specGet (ListType.cons (ListType Nat) rh rt) (Nat.succ jp)) (OptionType.some (ListType Nat) rv)) => Eq.substType Bool (fun (bb : Bool) => Eq (OptionType RecRule) (opt_pick RecRule bb (RecRule.mk (ctorName f jb) (sigLength rh) (mutRecRhs msig u gb rh)) (recrule_in_rules (mutRecRulesSig msig u f (Nat.add gb (Nat.succ Nat.zero)) (Nat.add jb (Nat.succ Nat.zero)) rt) (ctorName f (Nat.add jb (Nat.succ jp))))) (OptionType.some RecRule (RecRule.mk (ctorName f (Nat.add jb (Nat.succ jp))) (sigLength rv) (mutRecRhs msig u (Nat.add gb (Nat.succ jp)) rv)))) Bool.false (name_eqb (ctorName f jb) (ctorName f (Nat.add jb (Nat.succ jp)))) (Eq.symm Bool (name_eqb (ctorName f jb) (ctorName f (Nat.add jb (Nat.succ jp)))) Bool.false (Eq.trans Bool (name_eqb (ctorName f jb) (ctorName f (Nat.add jb (Nat.succ jp)))) (Bool.and Bool.true (nat_eqb jb (Nat.add jb (Nat.succ jp)))) Bool.false (Eq.cong Bool Bool (fun (bp : Bool) => Bool.and bp (nat_eqb jb (Nat.add jb (Nat.succ jp)))) (name_eqb f f) Bool.true (name_eqb_refl f)) (nat_eqb_self_add_succ_false jb jp))) (Eq.substType Nat (fun (jx : Nat) => Eq (OptionType RecRule) (recrule_in_rules (mutRecRulesSig msig u f (Nat.add gb (Nat.succ Nat.zero)) (Nat.add jb (Nat.succ Nat.zero)) rt) (ctorName f jx)) (OptionType.some RecRule (RecRule.mk (ctorName f jx) (sigLength rv) (mutRecRhs msig u (Nat.add gb (Nat.succ jp)) rv)))) (Nat.add (Nat.add jb (Nat.succ Nat.zero)) jp) (Nat.add jb (Nat.succ jp)) (nat_succ_add jb jp) (Eq.substType Nat (fun (gx : Nat) => Eq (OptionType RecRule) (recrule_in_rules (mutRecRulesSig msig u f (Nat.add gb (Nat.succ Nat.zero)) (Nat.add jb (Nat.succ Nat.zero)) rt) (ctorName f (Nat.add (Nat.add jb (Nat.succ Nat.zero)) jp))) (OptionType.some RecRule (RecRule.mk (ctorName f (Nat.add (Nat.add jb (Nat.succ Nat.zero)) jp)) (sigLength rv) (mutRecRhs msig u gx rv)))) (Nat.add (Nat.add gb (Nat.succ Nat.zero)) jp) (Nat.add gb (Nat.succ jp)) (nat_succ_add gb jp) (ih (Nat.add gb (Nat.succ Nat.zero)) (Nat.add jb (Nat.succ Nat.zero)) jp rv hs)))) jo hh) sig g0 j0 j rs h",
            "mutRecRulesSig_lookup: recrule_in_rules finds ctor (i,j)'s rule in the signature-built rule list. ListType.rec over the remaining ctors with an inner Nat.rec offset split; the two-counter analogue of genRecRulesFrom_lookup. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def mutREnv_ok_of (msig : ListType FamSpec) (u : Level) (hd : forall (ia : Nat) (ib2 : Nat), Lt ia (famCount msig) -> Lt ib2 (famCount msig) -> (Eq Nat ia ib2 -> Empty) -> Eq Bool (name_eqb (famNameAt msig ia) (famNameAt msig ib2)) Bool.false) : MutRecEnvOK msig u (mutREnv msig u) := MutRecEnvOK.mk msig u (mutREnv msig u) (fun (i : Nat) (hi : Lt i (famCount msig)) => Eq.substType Nat (fun (w : Nat) => Eq (OptionType RecMeta) (recmeta_for (mutREnv msig u) (mutRecName msig w)) (OptionType.some RecMeta (mutRecMeta msig))) (Nat.add Nat.zero i) i (nat_zero_add i) (mutREnvFrom_meta_lookup msig u hd (famCount msig) Nat.zero i hi (Eq.substType Nat (fun (w : Nat) => Lt w (famCount msig)) i (Nat.add Nat.zero i) (Eq.symm Nat (Nat.add Nat.zero i) i (nat_zero_add i)) hi))) (fun (i : Nat) (j : Nat) (rs : ListType Nat) (h : Eq (OptionType (ListType Nat)) (ctorSpecAt msig i j) (OptionType.some (ListType Nat) rs)) => Eq.substType (OptionType RecRules) (fun (o : OptionType RecRules) => Eq (OptionType RecRule) (OptionType.rec RecRules (fun (_o2 : OptionType RecRules) => OptionType RecRule) (OptionType.none RecRule) (fun (rules : RecRules) => recrule_in_rules rules (ctorName (famNameAt msig i) j)) o) (OptionType.some RecRule (RecRule.mk (ctorName (famNameAt msig i) j) (sigLength rs) (mutRecRhs msig u (Nat.add (mutOffset msig i) j) rs)))) (OptionType.some RecRules (mutRecRules msig u i)) (recrules_for (mutREnv msig u) (mutRecName msig i)) (Eq.symm (OptionType RecRules) (recrules_for (mutREnv msig u) (mutRecName msig i)) (OptionType.some RecRules (mutRecRules msig u i)) (Eq.substType Nat (fun (w : Nat) => Eq (OptionType RecRules) (recrules_for (mutREnv msig u) (mutRecName msig w)) (OptionType.some RecRules (mutRecRules msig u w))) (Nat.add Nat.zero i) i (nat_zero_add i) (mutREnvFrom_rules_lookup msig u hd (famCount msig) Nat.zero i (ctorSpecAt_lt msig j rs i h) (Eq.substType Nat (fun (w : Nat) => Lt w (famCount msig)) i (Nat.add Nat.zero i) (Eq.symm Nat (Nat.add Nat.zero i) i (nat_zero_add i)) (ctorSpecAt_lt msig j rs i h))))) (Eq.substType Nat (fun (w : Nat) => Eq (OptionType RecRule) (recrule_in_rules (mutRecRules msig u i) (ctorName (famNameAt msig i) w)) (OptionType.some RecRule (RecRule.mk (ctorName (famNameAt msig i) w) (sigLength rs) (mutRecRhs msig u (Nat.add (mutOffset msig i) j) rs)))) (Nat.add Nat.zero j) j (nat_zero_add j) (mutRecRulesSig_lookup msig u (famNameAt msig i) (famSigAt msig i) (mutOffset msig i) Nat.zero j rs h)))",
            "mutREnv_ok_of: MutRecEnvOK msig u (mutREnv msig u) from the distinctness fact and the two lookup lemmas, with its hypotheses carried EXPLICITLY rather than discharged -- the same idiom whnfAcc_const and supApp_step_inv use. MutSchema adequacy Phase 2.",
        )?;

        self.add_recursive_def(
            "def mutREnv_ok (msig : ListType FamSpec) (u : Level) (hdp : FamNamesDistinct msig) : MutRecEnvOK msig u (mutREnv msig u) := mutREnv_ok_of msig u (famNamesDistinct_fact msig hdp)",
            "mutREnv_ok: MutRecEnvOK msig u (mutREnv msig u) given FamNamesDistinct msig. The concrete env-OK witness for the mutual lane; the earlier recon flagged this as the known-hard item of the tower. MutSchema adequacy Phase 2.",
        )?;

        Ok(())
    }
}

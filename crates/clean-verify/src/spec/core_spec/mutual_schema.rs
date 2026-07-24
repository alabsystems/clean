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
//! This module registers the OBJECT LAYER in dependency order. Brick M1 (this
//! commit): FamSpec + accessors + block arithmetic + per-family recursor
//! names/consts/motives. Follow-on bricks: M1a telescopes, M1b rule-rhs, M1c
//! env, M4 K=1 degeneration bridges to the existing genRec* objects, then the
//! four theorem ports. Census stays PINNED at 11.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Mutual-schema rung, Brick M1: the FamSpec block element, its accessors,
    /// the block-arithmetic helpers (family/ctor counts, offsets, lookups), and
    /// the per-family recursor names/constants/motive types. Reuses only the
    /// existing SnSchema `famTypeC` + foundation Nat/Name/ListType/OptionType;
    /// registered after `add_snschema`/`add_univ_poly` (terminal lemma layer).
    pub(super) fn add_mutual_schema(&mut self) -> Result<(), SpecError> {
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

        Ok(())
    }
}

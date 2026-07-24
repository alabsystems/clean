// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Definitional extension judgments and soundness proofs for Phase 4 (#460).
//!
//! Formalizes: KEnv, ConstantExtension, InductiveExtension, DefinitionalExtension
//! (reflexive-transitive closure), and the derived `definitional_extension_sound`
//! theorem proving that any chain of extensions preserves EnvSound.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_env_extensions(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // PART 20: Definitional extensions
        // =========================================================
        //
        // The core KExpr model is intentionally environment-free. This slice
        // adds an explicit environment-extension judgment layer on top of it so
        // Phase 4 can state and compose soundness obligations for constants and
        // inductives without rewriting the whole typing relation in one step.

        self.add_inductive(
            r"inductive ConstExtensionKind : Type
| reducible_ : ConstExtensionKind
| opaque_ : ConstExtensionKind",
            "Kinds of constant definitional extensions: reducible definitions and opaque constants.",
        )?;

        self.add_inductive(
            r"inductive CtorDecl : Type
| mk : Nat -> KExpr -> CtorDecl",
            "Constructor declaration payload: numeric identifier and constructor type.",
        )?;

        self.add_inductive(
            r"inductive CtorDecls : Type
| nil : CtorDecls
| cons : CtorDecl -> CtorDecls -> CtorDecls",
            "Constructor declaration lists for inductive extension judgments.",
        )?;

        self.add_inductive(
            r"inductive KEnv : Type
| empty : KEnv
| addConst : KEnv -> ConstExtensionKind -> Nat -> KExpr -> KExpr -> KEnv
| addInductive : KEnv -> Nat -> Nat -> KExpr -> CtorDecls -> KEnv",
            "Specification environment for definitional extensions: empty, constant extension, or inductive extension.",
        )?;

        // kenv_fresh: the COMPUTABLE freshness fold over the KEnv extension chain —
        // decl_id is unused iff it differs from every bound decl_id in the chain.
        // KEnv is a finite inductive (empty / addConst / addInductive), so this is
        // a genuine structural recursion. Formerly FreshDeclName was an opaque
        // HelperAxiom; this makes it a real definition (the #2859 const_whnf pattern).
        self.add_recursive_def(
            r"def kenv_fresh (env : KEnv) (target : Nat) : Bool := match env with
| KEnv.empty => Bool.true
| KEnv.addConst env' kind id ty value => Bool.and (Bool.not (nat_eqb id target)) (kenv_fresh env' target)
| KEnv.addInductive env' id num_params ind_ty ctors => Bool.and (Bool.not (nat_eqb id target)) (kenv_fresh env' target)",
            "Computable freshness: kenv_fresh env target = true iff target is unused as a \
             declaration id anywhere in the KEnv extension chain (a structural KEnv fold, \
             nat_eqb-comparing each bound id).",
        )?;

        // FreshDeclName: was an opaque `KEnv -> Nat -> Type` HelperAxiom; now a
        // faithful reducible Prop DEFINITION over the computable kenv_fresh — the
        // REAL freshness condition, not an opaque token (the const_whnf drain
        // pattern). Semireducible so it unfolds to the Eq during declaration
        // checking. Consumers only RECEIVE FreshDeclName as a hypothesis (nothing
        // constructs it), so the Type->Prop change is transparent to them; the
        // ConstantExtension/InductiveExtension .mk premise fields become Prop.
        self.add_definition_reducible(SpecDefinition {
            name: "FreshDeclName".to_string(),
            type_src: "KEnv -> Nat -> Prop".to_string(),
            value_src: Some(
                "fun (env : KEnv) (decl_id : Nat) => Eq Bool (kenv_fresh env decl_id) Bool.true"
                    .to_string(),
            ),
            is_axiom: false,
            description: "FreshDeclName env decl_id: decl_id is unused in env, DEFINED as \
                          kenv_fresh env decl_id = true (the computable structural freshness \
                          fold). Formerly an opaque HelperAxiom; now a faithful definition."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kenv_fresh".to_string(),
                "Eq".to_string(),
                "Bool".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── Strict positivity: FAITHFUL computable algorithm ────────────────
        //
        // StrictlyPositiveCtorDecls was an opaque `KExpr -> CtorDecls -> Type`
        // HelperAxiom. It is now the REAL strict-positivity check as computable
        // Bool folds over KExpr (the const_whnf/kenv_fresh drain pattern),
        // adversarially verified (rejects (I->Bool)->I, (I->Empty)->I, nested
        // negatives; accepts (Bool->I)->I, (Nat->I)->I).
        //
        // CONVENTION (pinned): each ctor type lives under ONE outer binder for the
        // inductive I, so I = KExpr.bvar 0 at the ctor-type top, index +1 per
        // binder crossed. Env-free-faithful: the spec Typing is environment-free
        // with no Name<->decl_id bridge, so positional self-reference is the only
        // principled choice (consistent with WellFormedCtorDecls' return-head check).

        // occurs_in depth e: does I (= bvar depth, +1 per binder) occur in e?
        self.add_recursive_def(
            r"def occurs_in (depth : Nat) (e : KExpr) : Bool := match e with
| KExpr.sort n => Bool.false
| KExpr.bvar i => nat_eqb i depth
| KExpr.app f a => Bool.or (occurs_in depth f) (occurs_in depth a)
| KExpr.lam ty b => Bool.or (occurs_in depth ty) (occurs_in (Nat.succ depth) b)
| KExpr.pi ty b => Bool.or (occurs_in depth ty) (occurs_in (Nat.succ depth) b)
| KExpr.const n us => Bool.false
| KExpr.let_ ty v b => Bool.or (occurs_in depth ty) (Bool.or (occurs_in depth v) (occurs_in (Nat.succ depth) b))
| KExpr.proj s i sub => occurs_in depth sub
| KExpr.lit n => Bool.false",
            "occurs_in depth e: the inductive self-reference (de Bruijn bvar depth, \
             shifted +1 under each lam/pi binder) occurs somewhere in e.",
        )?;

        // positive_app depth e: e is an app spine headed by I with all args I-free.
        self.add_recursive_def(
            r"def positive_app (depth : Nat) (e : KExpr) : Bool := match e with
| KExpr.sort n => Bool.false
| KExpr.bvar i => nat_eqb i depth
| KExpr.app f a => Bool.and (positive_app depth f) (Bool.not (occurs_in depth a))
| KExpr.lam ty b => Bool.false
| KExpr.pi ty b => Bool.false
| KExpr.const n us => Bool.false
| KExpr.let_ ty v b => Bool.false
| KExpr.proj s i e => Bool.false
| KExpr.lit n => Bool.false",
            "positive_app depth e: e is an application spine whose head is the \
             inductive I (bvar depth) and I occurs in none of the spine arguments \
             (the strictly-positive app case; the bare bvar is the 0-argument spine).",
        )?;

        // strictly_positive_in depth e: I occurs only strictly positively in field type e.
        self.add_recursive_def(
            r"def strictly_positive_in (depth : Nat) (e : KExpr) : Bool := match e with
| KExpr.sort n => Bool.true
| KExpr.bvar i => Bool.true
| KExpr.app f a => Bool.or (Bool.not (Bool.or (occurs_in depth f) (occurs_in depth a))) (Bool.and (positive_app depth f) (Bool.not (occurs_in depth a)))
| KExpr.lam ty b => Bool.not (Bool.or (occurs_in depth ty) (occurs_in (Nat.succ depth) b))
| KExpr.pi dom cod => Bool.and (Bool.not (occurs_in depth dom)) (strictly_positive_in (Nat.succ depth) cod)
| KExpr.const n us => Bool.true
| KExpr.let_ ty v b => Bool.not (Bool.or (occurs_in depth ty) (Bool.or (occurs_in depth v) (occurs_in (Nat.succ depth) b)))
| KExpr.proj s i sub => Bool.not (occurs_in depth sub)
| KExpr.lit n => Bool.true",
            "strictly_positive_in depth e: the inductive I occurs only strictly \
             positively in the field type e. Pi-arm (the kernel rule): the domain \
             must be I-free AND I strictly positive in the codomain. App-arm: I \
             absent, or I heads a positive spine. Rejects any occurrence of I to the \
             left of an arrow (a negative position).",
        )?;

        // ctor_positive depth e: peel the ctor's own Pi telescope; each field domain
        // must be strictly_positive_in; the (non-Pi) return type is WellFormed's job.
        self.add_recursive_def(
            r"def ctor_positive (depth : Nat) (e : KExpr) : Bool := match e with
| KExpr.sort n => Bool.true
| KExpr.bvar i => Bool.true
| KExpr.app f a => Bool.true
| KExpr.lam ty b => Bool.true
| KExpr.pi dom cod => Bool.and (strictly_positive_in depth dom) (ctor_positive (Nat.succ depth) cod)
| KExpr.const n us => Bool.true
| KExpr.let_ ty v b => Bool.true
| KExpr.proj s i sub => Bool.true
| KExpr.lit n => Bool.true",
            "ctor_positive depth e: every field domain in the constructor type's own \
             Pi telescope is strictly_positive_in; recurse into the codomain at \
             depth+1. Stops (true) at the return type — return-shape is \
             WellFormedCtorDecls' obligation, not positivity's.",
        )?;

        // ctor_decl_type: the KExpr type out of CtorDecl.mk id ty.
        self.add_recursive_def(
            r"def ctor_decl_type (c : CtorDecl) : KExpr := match c with
| CtorDecl.mk id ty => ty",
            "ctor_decl_type c: projects the constructor type from CtorDecl.mk id ty.",
        )?;

        // strictly_positive_ctors_b: every ctor type positive, at depth 0 (I = bvar 0).
        self.add_recursive_def(
            r"def strictly_positive_ctors_b (ctors : CtorDecls) : Bool := match ctors with
| CtorDecls.nil => Bool.true
| CtorDecls.cons c rest => Bool.and (ctor_positive Nat.zero (ctor_decl_type c)) (strictly_positive_ctors_b rest)",
            "strictly_positive_ctors_b ctors: fold requiring every constructor type to \
             be ctor_positive at depth 0 (I = bvar 0 at each ctor-type top).",
        )?;

        // StrictlyPositiveCtorDecls: the opaque HelperAxiom, now a faithful reducible
        // Prop DEFINITION over strictly_positive_ctors_b (the FreshDeclName pattern).
        // ind_ty is bound-but-unused: positivity is fully determined by the ctor types
        // (matching the kernel's check_positivity). Type->Prop is transparent to the
        // sole consumer (InductiveExtension.mk premise, passed through, never destructed).
        self.add_definition_reducible(SpecDefinition {
            name: "StrictlyPositiveCtorDecls".to_string(),
            type_src: "KExpr -> CtorDecls -> Prop".to_string(),
            value_src: Some(
                "fun (ind_ty : KExpr) (ctors : CtorDecls) => Eq Bool (strictly_positive_ctors_b ctors) Bool.true"
                    .to_string(),
            ),
            is_axiom: false,
            description:
                "StrictlyPositiveCtorDecls ind_ty ctors: every constructor is strictly \
                 positive in the inductive being defined, DEFINED as \
                 strictly_positive_ctors_b ctors = true (the faithful computable \
                 strict-positivity algorithm — rejects negative occurrences). Formerly \
                 an opaque HelperAxiom."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "strictly_positive_ctors_b".to_string(),
                "Eq".to_string(),
                "Bool".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ── WellFormedCtorDecls: FAITHFUL (structural) + CtxTyping (typing) ──
        //
        // WellFormedCtorDecls was an opaque `KEnv -> Nat -> Nat -> KExpr ->
        // CtorDecls -> Type` HelperAxiom. It is now a genuine inductive whose mk
        // discharges the real kernel add_inductive constructor obligations:
        //   O1 result-level pinning (Eq (return_type ind_ty) (sort rlvl) — also
        //      rejects a non-normal ind_ty),
        //   O2 constructor well-typedness (CtxTyping in context [ind_ty]),
        //   O3 per-field universe bound (FieldsBounded: each field sort <= rlvl,
        //      skipped when rlvl = 0 / Prop),
        //   O4/O5 return-spine head = the inductive self-ref + the leading
        //      num_params args = the parameter bvars in order (ctor_decls_wf_b),
        //   O7 arity guard num_params <= count_pi.
        // (O6 strict positivity is the sibling StrictlyPositiveCtorDecls.)
        //
        // SOUNDNESS / HONEST INCOMPLETENESS (adversarially verified across four
        // rounds — caught + fixed a universe-mismatch, a dropped-return-arg, and a
        // VACUITY where the env-free Typing has no `var` rule): O2/O3 route ctor
        // typing through CtxTyping, the model's CONV-FREE, CONST-FREE
        // syntax-directed fragment. It is SOUND (never accepts a malformed ctor)
        // and NON-VACUOUS (CtxTyping.var types the self-ref, so e.g.
        // `I : Type | mk : I` and `mk : I -> I` are expressible), but
        // CONSERVATIVELY INCOMPLETE in TWO documented ways, each REJECT-ONLY:
        //   (a) CONVERSION — CtxTyping omits the conv rule (gated on
        //       DefEq-consistency, per CtxTyping's own status), so a ctor whose
        //       well-typedness needs definitional unfolding is rejected;
        //   (b) CONST-typed fields — CtxTyping has no const rule, so a field/param
        //       whose type is headed by a declared constant (Nat, Bool, other
        //       inductives) is rejected. Only "pure" (const-free-field) inductives
        //       are currently expressible.
        // This is NOT full kernel parity; it is the honest CtxTyping-fragment
        // model. Draining the opaque axiom to this real inductive is a genuine
        // census drop (no new axiom: CtxTyping is a pre-existing non-axiom).

        // nat_leb a b: a <= b via truncated subtraction.
        self.add_recursive_def(
            r"def nat_leb (a : Nat) (b : Nat) : Bool := nat_is_zero (Nat.sub a b)",
            "nat_leb a b = true iff a <= b (nat_is_zero of the truncated difference).",
        )?;

        // count_pi e: the number of leading Pi binders (the telescope length).
        self.add_recursive_def(
            r"def count_pi (e : KExpr) : Nat := match e with
| KExpr.sort n => Nat.zero
| KExpr.bvar i => Nat.zero
| KExpr.app f a => Nat.zero
| KExpr.lam ty b => Nat.zero
| KExpr.pi dom cod => Nat.succ (count_pi cod)
| KExpr.const n us => Nat.zero
| KExpr.let_ ty v b => Nat.zero
| KExpr.proj s i sub => Nat.zero
| KExpr.lit n => Nat.zero",
            "count_pi e: the length of e's leading Pi telescope.",
        )?;

        // return_type e: strip the whole Pi telescope (kernel get_return_type).
        self.add_recursive_def(
            r"def return_type (e : KExpr) : KExpr := match e with
| KExpr.sort n => KExpr.sort n
| KExpr.bvar i => KExpr.bvar i
| KExpr.app f a => KExpr.app f a
| KExpr.lam ty b => KExpr.lam ty b
| KExpr.pi dom cod => return_type cod
| KExpr.const n us => KExpr.const n us
| KExpr.let_ ty v b => KExpr.let_ ty v b
| KExpr.proj s i sub => KExpr.proj s i sub
| KExpr.lit n => KExpr.lit n",
            "return_type e: e with its leading Pi telescope stripped (get_return_type).",
        )?;

        // is_bvar_eq k e: e is exactly the de Bruijn variable k.
        self.add_recursive_def(
            r"def is_bvar_eq (k : Nat) (e : KExpr) : Bool := match e with
| KExpr.sort n => Bool.false
| KExpr.bvar i => nat_eqb i k
| KExpr.app f a => Bool.false
| KExpr.lam ty b => Bool.false
| KExpr.pi ty b => Bool.false
| KExpr.const n us => Bool.false
| KExpr.let_ ty v b => Bool.false
| KExpr.proj s i e => Bool.false
| KExpr.lit n => Bool.false",
            "is_bvar_eq k e: e is exactly KExpr.bvar k.",
        )?;

        // return_arg_ok d np a: the parameter arg at this spine position is the
        // expected param bvar (bvar (d - np), where d = count_pi and np counts down).
        self.add_recursive_def(
            r"def return_arg_ok (d : Nat) (np : Nat) (a : KExpr) : Bool := is_bvar_eq (Nat.sub d np) a",
            "return_arg_ok d np a: the return-spine parameter arg a equals bvar (d - np).",
        )?;

        // return_args_wf_from d np e: the return spine (walked outermost-first) is
        // headed by the inductive self-ref bvar d and re-applies exactly the np
        // parameter bvars in order.
        self.add_recursive_def(
            r"def return_args_wf_from (d : Nat) (np : Nat) (e : KExpr) : Bool := match e with
| KExpr.sort n => Bool.false
| KExpr.bvar i => Bool.and (nat_eqb i d) (nat_is_zero np)
| KExpr.app f a => Bool.and (Bool.not (nat_is_zero np)) (Bool.and (return_arg_ok d np a) (return_args_wf_from d (Nat.sub np (Nat.succ Nat.zero)) f))
| KExpr.lam ty b => Bool.false
| KExpr.pi ty b => Bool.false
| KExpr.const n us => Bool.false
| KExpr.let_ ty v b => Bool.false
| KExpr.proj s i e => Bool.false
| KExpr.lit n => Bool.false",
            "return_args_wf_from d np e: the return application spine is headed by \
             the self-ref bvar d and its deepest np args are the parameter bvars in \
             order (rejects wrong head / order / count).",
        )?;

        // ctor_return_wf_b: arity guard + return-spine structural check.
        self.add_recursive_def(
            r"def ctor_return_wf_b (num_params : Nat) (ct : KExpr) : Bool := Bool.and (nat_leb num_params (count_pi ct)) (return_args_wf_from (count_pi ct) num_params (return_type ct))",
            "ctor_return_wf_b num_params ct: the telescope has at least num_params \
             binders AND its return spine is the inductive applied to the params.",
        )?;

        self.add_recursive_def(
            r"def ctor_wf_b (num_params : Nat) (c : CtorDecl) : Bool := ctor_return_wf_b num_params (ctor_decl_type c)",
            "ctor_wf_b num_params c: ctor_return_wf_b on the constructor's type.",
        )?;

        self.add_recursive_def(
            r"def ctor_decls_wf_b (num_params : Nat) (ctors : CtorDecls) : Bool := match ctors with
| CtorDecls.nil => Bool.true
| CtorDecls.cons c rest => Bool.and (ctor_wf_b num_params c) (ctor_decls_wf_b num_params rest)",
            "ctor_decls_wf_b: every constructor passes the structural return check.",
        )?;

        // level_is_zero / level_eqb / level_leb: in-bundle universe-level helpers
        // for FieldsBounded's per-field bound, now that KExpr.sort carries a full
        // kernel Level (task #29). (kexpr_beq.rs defines level_is_zero/level_eqb too,
        // but that module is registered only in its own disjoint test spec — never in
        // this bundle — so there is no name collision.)
        self.add_recursive_def(
            r"def level_is_zero (l : Level) : Bool := match l with
| Level.zero => Bool.true
| Level.succ p => Bool.false
| Level.max l1 l2 => Bool.and (level_is_zero l1) (level_is_zero l2)
| Level.imax l1 l2 => level_is_zero l2
| Level.param p => Bool.false",
            "level_is_zero l = true iff l is definitely universe zero (sound: max both-zero, imax by l2, succ/param never).",
        )?;
        self.add_recursive_def(
            concat!(
                "def level_eqb (a : Level) (b : Level) : Bool := ",
                "Level.rec (fun (_ : Level) => Level -> Bool) ",
                "(fun (y : Level) => Level.rec (fun (_ : Level) => Bool) ",
                "Bool.true ",
                "(fun (yp : Level) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yn : Name) => Bool.false) y) ",
                "(fun (ap : Level) (ih_ap : Level -> Bool) => fun (y : Level) => ",
                "Level.rec (fun (_ : Level) => Bool) ",
                "Bool.false ",
                "(fun (yp : Level) (_ : Bool) => ih_ap yp) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yn : Name) => Bool.false) y) ",
                "(fun (al : Level) (ar : Level) (ih_al : Level -> Bool) (ih_ar : Level -> Bool) => ",
                "fun (y : Level) => Level.rec (fun (_ : Level) => Bool) ",
                "Bool.false ",
                "(fun (yp : Level) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.and (ih_al yl) (ih_ar yr)) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yn : Name) => Bool.false) y) ",
                "(fun (al : Level) (ar : Level) (ih_al : Level -> Bool) (ih_ar : Level -> Bool) => ",
                "fun (y : Level) => Level.rec (fun (_ : Level) => Bool) ",
                "Bool.false ",
                "(fun (yp : Level) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.and (ih_al yl) (ih_ar yr)) ",
                "(fun (yn : Name) => Bool.false) y) ",
                "(fun (am : Name) => fun (y : Level) => Level.rec (fun (_ : Level) => Bool) ",
                "Bool.false ",
                "(fun (yp : Level) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yl : Level) (yr : Level) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yn : Name) => name_eqb am yn) y) ",
                "a b",
            ),
            "Boolean equality on universe levels (verbatim from kexpr_beq; param compares Names via name_eqb).",
        )?;
        // level_leb s r: SOUND, deliberately conservative field-universe bound.
        // true only when s is definitely zero (0 <= r) or s = r (r <= r) -> s <= r in
        // every valuation. Honest incompleteness: it does NOT prove e.g. a <= max a b;
        // that is reject-only (never accepts an unsound field), which is all soundness
        // needs. No witness currently constructs FieldsBounded.field, so completeness
        // is unobservable; it only has to elaborate soundly. Replaces the old Nat
        // nat_leb, which no longer typechecks now that the field sort s is a Level.
        self.add_recursive_def(
            r"def level_leb (s : Level) (r : Level) : Bool := Bool.or (level_is_zero s) (level_eqb s r)",
            "level_leb s r = true implies s <= r (sound, conservative: only s=0 or s=r). Field-universe bound for FieldsBounded.",
        )?;

        // FieldsBounded rlvl gamma rp ct: peel ct's Pi telescope in context gamma
        // (starting [ind_ty]); the first `rp` (= num_params) binders are params
        // (typed, NOT universe-bounded); each remaining FIELD's sort s is typed by
        // CtxTyping AND bounded s <= rlvl (skipped when rlvl = 0 / Prop). done_*
        // terminate at a non-Pi return head (its correctness is ctor_return_wf_b's
        // job). No done for KExpr.lam: a lambda return head is soundly rejected.
        self.add_inductive(
            r"inductive FieldsBounded : Level -> ListType KExpr -> Nat -> KExpr -> Type
| param : forall (rlvl : Level) (gamma : ListType KExpr) (rp : Nat) (dom : KExpr) (cod : KExpr) (s : Level), CtxTyping gamma dom (KExpr.sort s) -> FieldsBounded rlvl (ListType.cons KExpr dom gamma) rp cod -> FieldsBounded rlvl gamma (Nat.succ rp) (KExpr.pi dom cod)
| field : forall (rlvl : Level) (gamma : ListType KExpr) (dom : KExpr) (cod : KExpr) (s : Level), CtxTyping gamma dom (KExpr.sort s) -> Eq Bool (Bool.or (level_is_zero rlvl) (level_leb s rlvl)) Bool.true -> FieldsBounded rlvl (ListType.cons KExpr dom gamma) Nat.zero cod -> FieldsBounded rlvl gamma Nat.zero (KExpr.pi dom cod)
| done_sort : forall (rlvl : Level) (gamma : ListType KExpr) (n : Level), FieldsBounded rlvl gamma Nat.zero (KExpr.sort n)
| done_bvar : forall (rlvl : Level) (gamma : ListType KExpr) (i : Nat), FieldsBounded rlvl gamma Nat.zero (KExpr.bvar i)
| done_app : forall (rlvl : Level) (gamma : ListType KExpr) (f : KExpr) (a : KExpr), FieldsBounded rlvl gamma Nat.zero (KExpr.app f a)
| done_const : forall (rlvl : Level) (gamma : ListType KExpr) (nm : Name) (us : ListType Level), FieldsBounded rlvl gamma Nat.zero (KExpr.const nm us)",
            "FieldsBounded rlvl gamma rp ct: the constructor telescope ct, under \
             context gamma, peels rp parameter binders then bounds every field's \
             universe level by rlvl (Prop-skip via nat_is_zero rlvl). Field typing is \
             CtxTyping (conv-free, const-free fragment).",
        )?;

        // CtorsWellTyped rlvl num_params ind_ty ctors: every ctor type is well-typed
        // in context [ind_ty] (CtxTyping, so the self-ref is typed) AND satisfies the
        // per-field universe bound (FieldsBounded).
        self.add_inductive(
            r"inductive CtorsWellTyped : Level -> Nat -> KExpr -> CtorDecls -> Type
| nil : forall (rlvl : Level) (num_params : Nat) (ind_ty : KExpr), CtorsWellTyped rlvl num_params ind_ty CtorDecls.nil
| cons : forall (rlvl : Level) (num_params : Nat) (ind_ty : KExpr) (id : Nat) (ct : KExpr) (u : Level) (rest : CtorDecls), CtxTyping (ListType.cons KExpr ind_ty (ListType.nil KExpr)) ct (KExpr.sort u) -> FieldsBounded rlvl (ListType.cons KExpr ind_ty (ListType.nil KExpr)) num_params ct -> CtorsWellTyped rlvl num_params ind_ty rest -> CtorsWellTyped rlvl num_params ind_ty (CtorDecls.cons (CtorDecl.mk id ct) rest)",
            "CtorsWellTyped rlvl num_params ind_ty ctors: each constructor type is \
             CtxTyping-well-typed in context [ind_ty] and universe-bounded by rlvl. \
             SOUND but conv-free + const-free incomplete (see WellFormedCtorDecls).",
        )?;

        // WellFormedCtorDecls: drained from the opaque HelperAxiom to this inductive.
        // Same 5-arg signature so InductiveExtension.mk's premise threads unchanged.
        self.add_inductive(
            r"inductive WellFormedCtorDecls : KEnv -> Nat -> Nat -> KExpr -> CtorDecls -> Type
| mk : forall (env : KEnv) (decl_id : Nat) (num_params : Nat) (ind_ty : KExpr) (ctors : CtorDecls) (rlvl : Level), Eq KExpr (return_type ind_ty) (KExpr.sort rlvl) -> Eq Bool (ctor_decls_wf_b num_params ctors) Bool.true -> CtorsWellTyped rlvl num_params ind_ty ctors -> WellFormedCtorDecls env decl_id num_params ind_ty ctors",
            "WellFormedCtorDecls env decl_id num_params ind_ty ctors: constructor-side \
             well-formedness, DRAINED from an opaque HelperAxiom to a genuine inductive. \
             mk pins the result level (Eq return_type ind_ty = sort rlvl, also rejecting \
             non-normal formers), structurally checks every return spine \
             (ctor_decls_wf_b: head = self-ref, first num_params args = the param bvars \
             in order, arity guard), and delegates constructor well-typedness + the \
             per-field universe bound to CtorsWellTyped. SOUND and NON-VACUOUS. HONEST \
             INCOMPLETENESS (reject-only, not unsound): constructor typing uses the \
             CONV-FREE, CONST-FREE CtxTyping fragment, so ctors needing conversion, or \
             with const-headed (Nat/Bool/other-inductive) field types, are rejected — \
             only pure inductives are currently expressible. NOT full kernel parity; \
             the conv/const extensions are gated on deeper obligations (DefEq-consistency \
             / a CtxTyping const rule). No new census axiom (CtxTyping is a non-axiom).",
        )?;

        // NON-VACUITY WITNESS (guards against a vacuous masquerade — round-3 found
        // the env-free Typing route was uninhabitable): an explicit, kernel-checked
        // WellFormedCtorDecls.mk term for the pure inductive `I : Type | mk : I`
        // (ind_ty = sort 1, num_params 0, one ctor whose type is the self-ref bvar 0).
        // If this DerivedProved def type-checks, WellFormedCtorDecls is inhabited, so
        // the drain is not a vacuity masquerade.
        self.add_definition(SpecDefinition {
            name: "well_formed_ctor_decls_nonvacuity_witness".to_string(),
            type_src:
                "WellFormedCtorDecls KEnv.empty Nat.zero Nat.zero (KExpr.sort (Level.succ Level.zero)) (CtorDecls.cons (CtorDecl.mk Nat.zero (KExpr.bvar Nat.zero)) CtorDecls.nil)"
                    .to_string(),
            value_src: Some(
                "WellFormedCtorDecls.mk KEnv.empty Nat.zero Nat.zero (KExpr.sort (Level.succ Level.zero)) (CtorDecls.cons (CtorDecl.mk Nat.zero (KExpr.bvar Nat.zero)) CtorDecls.nil) (Level.succ Level.zero) (Eq.refl KExpr (KExpr.sort (Level.succ Level.zero))) (Eq.refl Bool Bool.true) (CtorsWellTyped.cons (Level.succ Level.zero) Nat.zero (KExpr.sort (Level.succ Level.zero)) Nat.zero (KExpr.bvar Nat.zero) (Level.succ Level.zero) CtorDecls.nil (CtxTyping.var (ListType.cons KExpr (KExpr.sort (Level.succ Level.zero)) (ListType.nil KExpr)) Nat.zero (KExpr.sort (Level.succ Level.zero)) (CtxLookup.here (KExpr.sort (Level.succ Level.zero)) (ListType.nil KExpr))) (FieldsBounded.done_bvar (Level.succ Level.zero) (ListType.cons KExpr (KExpr.sort (Level.succ Level.zero)) (ListType.nil KExpr)) Nat.zero) (CtorsWellTyped.nil (Level.succ Level.zero) Nat.zero (KExpr.sort (Level.succ Level.zero))))"
                    .to_string(),
            ),
            is_axiom: false,
            description:
                "Non-vacuity witness: an explicit WellFormedCtorDecls.mk for I : Type | mk : I. \
                 Proves the drained WellFormedCtorDecls inductive is INHABITED (not a vacuous \
                 masquerade). DerivedProved, zero axiom_deps."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "WellFormedCtorDecls".to_string(),
                "CtorsWellTyped".to_string(),
                "FieldsBounded".to_string(),
                "CtxTyping".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ConstantExtension / InductiveExtension were previously HAND-AXIOMATIZED
        // inductives: for each, the TYPE and the single `mk` constructor were two
        // separate FoundationalRule axioms. They are now GENUINE inductives: the
        // `mk` constructor fields below transcribe the retired `.mk` axioms
        // VERBATIM (byte-identical modulo the `<T>.mk :` prefix), and the kernel
        // GENERATES ConstantExtension.rec / InductiveExtension.rec (checked, sound
        // by construction) — the same retirement applied to KernelAddDeclChain and
        // KernelDefEqAccepts. The opaque well-formedness predicates the `mk` fields
        // reference as premises (FreshDeclName / StrictlyPositiveCtorDecls /
        // WellFormedCtorDecls, registered above) remain HelperAxioms — draining
        // those is separate, harder work.
        //
        // RECURSOR SHAPE: the `mk` conclusion's FIRST family index `env` is uniform
        // (it is both the source-env argument and the `env` inside KEnv.addConst),
        // so fixed-index promotion (`fixedIndicesToParams`) promotes it to a
        // recursor PARAMETER; the SECOND index (the KEnv.addConst / KEnv.addInductive
        // spine) stays a computed index. No consumer applies ConstantExtension.rec
        // or InductiveExtension.rec (every use is a TYPE reference or a `.mk`
        // construction, both preserved byte-identically), so nothing downstream is
        // reshaped by this conversion.
        self.add_inductive(
            r"inductive ConstantExtension : KEnv -> KEnv -> Type
| mk : forall (env : KEnv) (kind : ConstExtensionKind) (decl_id : Nat) (ty : KExpr) (value : KExpr) (u : Level), FreshDeclName env decl_id -> Typing ty (KExpr.sort u) -> Typing value ty -> ConstantExtension env (KEnv.addConst env kind decl_id ty value)",
            "Immediate constant extension judgment: a well-typed definition or opaque \
             constant added to an environment. Faithful inductive (formerly 2 hand \
             axioms: the type and the mk constructor) — the kernel generates \
             ConstantExtension.rec, sound by construction. The single `mk` constructor \
             transcribes the retired ConstantExtension.mk axiom verbatim: a fresh \
             (FreshDeclName), well-typed (Typing ty : sort u, Typing value : ty) \
             constant body extends the environment via KEnv.addConst.",
        )?;

        self.add_inductive(
            r"inductive InductiveExtension : KEnv -> KEnv -> Type
| mk : forall (env : KEnv) (decl_id : Nat) (num_params : Nat) (ind_ty : KExpr) (ctors : CtorDecls) (u : Level), FreshDeclName env decl_id -> Typing ind_ty (KExpr.sort u) -> StrictlyPositiveCtorDecls ind_ty ctors -> WellFormedCtorDecls env decl_id num_params ind_ty ctors -> InductiveExtension env (KEnv.addInductive env decl_id num_params ind_ty ctors)",
            "Immediate inductive extension judgment: a fresh well-formed inductive \
             declaration added to an environment. Faithful inductive (formerly 2 hand \
             axioms: the type and the mk constructor) — the kernel generates \
             InductiveExtension.rec, sound by construction. The single `mk` constructor \
             transcribes the retired InductiveExtension.mk axiom verbatim: a fresh \
             (FreshDeclName), well-typed (Typing ind_ty : sort u), strictly-positive \
             (StrictlyPositiveCtorDecls), constructor-well-formed (WellFormedCtorDecls) \
             inductive block extends the environment via KEnv.addInductive.",
        )?;

        // =========================================================
        // DefinitionalExtension: reflexive-transitive closure (Part of #460)
        // =========================================================
        //
        // DefinitionalExtension was previously a HAND-AXIOMATIZED inductive: the
        // type, all four constructors (refl/const_/inductive_/trans) AND the
        // recursor were 6 separate FoundationalRule axioms (is_axiom:true,
        // value-less). It is now a GENUINE inductive registered via `add_inductive`
        // — the same retirement applied to DefEq / Typing / TypedDefEq (and the
        // sibling ConstantExtension / InductiveExtension above). Every constructor
        // type transcribes its retired axiom BYTE-IDENTICALLY (no strengthening/
        // weakening — this is exactly the standard reflexive-transitive closure over
        // the immediate constant/inductive extension steps), and the kernel
        // GENERATES `DefinitionalExtension.rec` (positivity-checked, sound by
        // construction). All 6 names now lower to non-Axiom kernel declarations
        // (Inductive / Constructor / Recursor) and leave the ConstantKind::Axiom
        // census.
        //
        // RECURSOR SHAPE (why the generated recursor matches the retired
        // hand-written one exactly, so every consumer elaborates unchanged): unlike
        // the sibling ConstantExtension / InductiveExtension — whose single non-
        // recursive `mk` lets fixedIndicesToParams promote the uniform FIRST index
        // `env` to a recursor parameter — DefinitionalExtension has the RECURSIVE
        // binary `trans` constructor, whose SECOND hypothesis `DefinitionalExtension
        // mid env'` carries `mid` (not the conclusion's source `env`) in the first
        // index position. The first index is therefore NON-UNIFORM across the
        // recursive occurrences, so fixedIndicesToParams does NOT promote it: both
        // KEnv arguments stay genuine INDICES (identical to DefEq / Typing, whose
        // recursive trans/symm constructors block promotion the same way). The
        // generated recursor keeps the 2-index motive
        // (`fun (env env' : KEnv) (h : DefinitionalExtension env env') => ...`) with
        // the minor-premise order refl -> const_ -> inductive_ -> trans, so the
        // `definitional_extension_sound` proof (the DefinitionalExtension.rec
        // consumer, mirrored in proofs/library_subst_micro_env.rs) and the
        // .refl/.const_/.inductive_/.trans construction sites (implementation_
        // soundness.rs, the EnvSound step lemmas below, the env-preservation bridges)
        // all type-check against the generated recursor/constructors unchanged. ZERO
        // new axioms. Part of the inductive-encoding drain (after DefEq / Typing /
        // TypedDefEq).
        self.add_inductive(
            concat!(
                "inductive DefinitionalExtension : KEnv -> KEnv -> Type\n",
                "| refl : forall (env : KEnv), DefinitionalExtension env env\n",
                "| const_ : forall (env : KEnv) (env' : KEnv), ConstantExtension env env' -> DefinitionalExtension env env'\n",
                "| inductive_ : forall (env : KEnv) (env' : KEnv), InductiveExtension env env' -> DefinitionalExtension env env'\n",
                "| trans : forall (env : KEnv) (mid : KEnv) (env' : KEnv), DefinitionalExtension env mid -> DefinitionalExtension mid env' -> DefinitionalExtension env env'"
            ),
            "Reflexive-transitive closure of constant and inductive definitional extension steps. Faithful four-constructor inductive (formerly 6 hand axioms: the type, refl/const_/inductive_/trans, and a hand-written recursor). refl is the zero-step chain; const_/inductive_ lift an immediate ConstantExtension / InductiveExtension step into the closure; trans composes two chains. Every constructor type is byte-identical to its retired axiom; the kernel generates DefinitionalExtension.rec, sound by construction. The recursive binary trans keeps both KEnv arguments as genuine indices (no fixed-index promotion), so the generated recursor matches the retired hand-written layout and every consumer elaborates unchanged. ZERO new axioms.",
        )?;

        // =========================================================
        // EnvSound: FAITHFUL definition (was a bare KEnv -> Type axiom).
        // =========================================================
        //
        // Soundness of a specification environment is DEFINED as: it is reachable
        // from the empty environment by a valid chain of definitional-extension
        // steps. This is not a vacuous Unit/always-true stand-in — it unfolds to
        // the real `DefinitionalExtension KEnv.empty env` reachability witness,
        // which itself carries the well-typedness side-conditions of every
        // constant/inductive step (FreshDeclName, Typing, StrictlyPositiveCtorDecls,
        // WellFormedCtorDecls) through the ConstantExtension/InductiveExtension
        // constructors. Registered semireducibly so the kernel unfolds it during
        // defeq when discharging the step-preservation theorems below.
        self.add_definition_reducible(SpecDefinition {
            name: "EnvSound".to_string(),
            type_src: "KEnv -> Type".to_string(),
            value_src: Some(
                "fun (env : KEnv) => DefinitionalExtension KEnv.empty env".to_string(),
            ),
            is_axiom: false,
            description:
                "Soundness of a specification environment, DEFINED as reachability from the empty environment by a valid definitional-extension chain (DefinitionalExtension KEnv.empty env). Faithful: it unfolds to the real reachability witness carrying every step's well-typedness side-conditions, NOT a vacuous always-true predicate."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["DefinitionalExtension".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // constant_extension_preserves_soundness: now a DERIVED THEOREM, not an
        // axiom. With EnvSound := DefinitionalExtension KEnv.empty env, preserving
        // soundness across one constant step is exactly transitivity of the
        // extension chain composed with lifting the immediate step into the
        // closure: trans empty env env' h_sound (const_ env env' h_ext).
        self.add_definition(SpecDefinition {
            name: "constant_extension_preserves_soundness".to_string(),
            type_src: "forall (env : KEnv) (env' : KEnv), ConstantExtension env env' -> EnvSound env -> EnvSound env'".to_string(),
            value_src: Some(
                concat!(
                    "fun (env : KEnv) (env' : KEnv) ",
                    "(h_ext : ConstantExtension env env') (h_sound : EnvSound env) => ",
                    "DefinitionalExtension.trans KEnv.empty env env' h_sound ",
                    "(DefinitionalExtension.const_ env env' h_ext)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description:
                "Derived: one constant extension step preserves soundness. Proof = transitivity of the definitional-extension chain (DefinitionalExtension.trans) composed with lifting the immediate constant step into the closure (DefinitionalExtension.const_). Kernel-type-checks against EnvSound unfolded to DefinitionalExtension KEnv.empty env; rests only on the FoundationalRule extension constructors, no helper axioms.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ConstantExtension".to_string(),
                "EnvSound".to_string(),
                "DefinitionalExtension.trans".to_string(),
                "DefinitionalExtension.const_".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // inductive_extension_preserves_soundness: derived analogously, lifting the
        // immediate inductive step via DefinitionalExtension.inductive_.
        self.add_definition(SpecDefinition {
            name: "inductive_extension_preserves_soundness".to_string(),
            type_src: "forall (env : KEnv) (env' : KEnv), InductiveExtension env env' -> EnvSound env -> EnvSound env'".to_string(),
            value_src: Some(
                concat!(
                    "fun (env : KEnv) (env' : KEnv) ",
                    "(h_ext : InductiveExtension env env') (h_sound : EnvSound env) => ",
                    "DefinitionalExtension.trans KEnv.empty env env' h_sound ",
                    "(DefinitionalExtension.inductive_ env env' h_ext)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description:
                "Derived: one inductive extension step preserves soundness. Proof = transitivity of the definitional-extension chain (DefinitionalExtension.trans) composed with lifting the immediate inductive step into the closure (DefinitionalExtension.inductive_). Kernel-type-checks against EnvSound unfolded to DefinitionalExtension KEnv.empty env; rests only on the FoundationalRule extension constructors, no helper axioms.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "InductiveExtension".to_string(),
                "EnvSound".to_string(),
                "DefinitionalExtension.trans".to_string(),
                "DefinitionalExtension.inductive_".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "definitional_extension_sound".to_string(),
            type_src: "forall (env : KEnv) (env' : KEnv), DefinitionalExtension env env' -> EnvSound env -> EnvSound env'".to_string(),
            value_src: Some(
                concat!(
                    "fun (env : KEnv) (env' : KEnv) ",
                    "(h_ext : DefinitionalExtension env env') ",
                    "(h_sound : EnvSound env) => ",
                    "DefinitionalExtension.rec ",
                    "(fun (src_env : KEnv) (dst_env : KEnv) (h_ext_step : DefinitionalExtension src_env dst_env) => EnvSound src_env -> EnvSound dst_env) ",
                    "(fun (base : KEnv) (base_sound : EnvSound base) => base_sound) ",
                    "(fun (src_env : KEnv) (dst_env : KEnv) (h_const : ConstantExtension src_env dst_env) ",
                    "(src_sound : EnvSound src_env) => ",
                    "constant_extension_preserves_soundness src_env dst_env h_const src_sound) ",
                    "(fun (src_env : KEnv) (dst_env : KEnv) (h_ind : InductiveExtension src_env dst_env) ",
                    "(src_sound : EnvSound src_env) => ",
                    "inductive_extension_preserves_soundness src_env dst_env h_ind src_sound) ",
                    "(fun (src_env : KEnv) (mid_env : KEnv) (dst_env : KEnv) ",
                    "(h_left : DefinitionalExtension src_env mid_env) ",
                    "(h_right : DefinitionalExtension mid_env dst_env) ",
                    "(ih_left : EnvSound src_env -> EnvSound mid_env) ",
                    "(ih_right : EnvSound mid_env -> EnvSound dst_env) ",
                    "(src_sound : EnvSound src_env) => ",
                    "ih_right (ih_left src_sound)) ",
                    "env env' h_ext h_sound"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Derived soundness theorem: any chain of definitional extensions preserves EnvSound. ",
                "The proof term is COMPLETE and kernel-type-checks (structural recursion via ",
                "DefinitionalExtension.rec; refl/trans cases are discharged constructively and are NOT ",
                "blocked by the iota seam or church_rosser). Now DerivedProved: EnvSound is a faithful ",
                "definition (DefinitionalExtension KEnv.empty env) and the two step lemmas ",
                "constant_extension_preserves_soundness / inductive_extension_preserves_soundness are ",
                "themselves derived from the FoundationalRule extension constructors (trans + const_/inductive_), ",
                "so the whole closure rests only on the trusted extension-judgment rules — no HelperAxioms remain. ",
                "Carried at DerivedPending in the static snapshot (matching the reducible-definition convention where ",
                "the promotion pipeline performs the DerivedProved upgrade); the promotion gate kernel-checks the full ",
                "recursor proof and computes an EMPTY helper-axiom closure (see tests)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedPending,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "DefinitionalExtension.rec".to_string(),
                "constant_extension_preserves_soundness".to_string(),
                "inductive_extension_preserves_soundness".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::types::{AxiomCategory, ProofStatus};
    use crate::spec::Specification;
    use crate::test_utils::build_spec_with_stack;

    /// Build the full core spec (on a large stack) for the definitional-extension
    /// tests.
    ///
    /// Formerly a hand-rolled minimal spec (Nat + a one-constructor KExpr + an
    /// opaque `Typing` axiom). That sufficed while the env-extension layer was
    /// entirely opaque `... -> Type` HelperAxioms. After the axiom-inductivization
    /// drains, `add_env_extensions` now registers REAL computable definitions and
    /// inductives — `kenv_fresh` over `nat_eqb`/`Bool`, the strict-positivity folds
    /// over the full `KExpr`, and `WellFormedCtorDecls`/`CtorsWellTyped` over
    /// `CtxTyping`/`ListType` — so the layer only elaborates against the full
    /// prerequisite stack (the minimal fixture panicked in `kenv_fresh`
    /// elaboration). The full spec supplies every prerequisite; each assertion
    /// below is unchanged and still targets exactly these env-extension definitions.
    fn build_env_extensions_spec() -> Specification {
        build_spec_with_stack()
    }

    #[test]
    fn zz_diagnostic_dump_extension_recursors() {
        let spec = build_env_extensions_spec();
        for name in [
            "ConstantExtension",
            "ConstantExtension.mk",
            "ConstantExtension.rec",
            "InductiveExtension",
            "InductiveExtension.mk",
            "InductiveExtension.rec",
        ] {
            let ty = spec
                .definitions()
                .get(name)
                .and_then(|d| d.elaborated_type.as_ref())
                .map(|t| format!("{t:?}"))
                .unwrap_or_else(|| "<no elaborated_type>".to_string());
            let is_axiom = spec.definitions().get(name).map(|d| d.is_axiom);
            let kind = spec
                .env()
                .get_const(&clean_kernel::Name::from_string(name))
                .map(|c| format!("{:?}", c.kind));
            println!("DIAG {name} is_axiom={is_axiom:?} kernel_kind={kind:?}\n  TYPE {ty}\n");
        }
    }

    #[test]
    fn test_definitional_extension_definitions_exist() {
        let spec = build_env_extensions_spec();
        for name in [
            "ConstExtensionKind",
            "CtorDecl",
            "CtorDecls",
            "KEnv",
            "ConstantExtension",
            "InductiveExtension",
            "DefinitionalExtension",
            "DefinitionalExtension.rec",
            "EnvSound",
            "definitional_extension_sound",
        ] {
            assert!(
                spec.definitions().contains_key(name),
                "Expected definitional-extension spec {name} to exist"
            );
        }
    }

    #[test]
    fn test_definitional_extension_sound_type_checks() {
        let spec = build_env_extensions_spec();
        spec.verify_definition("definitional_extension_sound")
            .expect("definitional_extension_sound should elaborate and type-check");
    }

    #[test]
    fn test_definitional_extension_sound_type_checks_in_full_spec() {
        let theorem = "definitional_extension_sound";
        let spec = build_spec_with_stack();
        assert!(
            spec.definitions().contains_key(theorem),
            "full core spec should register {theorem}"
        );
        spec.verify_definition(theorem)
            .expect("definitional_extension_sound should type-check in the full core spec");
    }

    /// The lemma is a real derived theorem (not an axiom restatement): it has a
    /// constructive value term and `is_axiom == false`.
    #[test]
    fn test_definitional_extension_sound_is_derived_lemma_not_axiom() {
        let spec = build_env_extensions_spec();
        let def = spec
            .definitions()
            .get("definitional_extension_sound")
            .expect("definitional_extension_sound should exist");
        assert!(
            !def.is_axiom,
            "definitional_extension_sound carries a proof term and must not be an axiom"
        );
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "definitional_extension_sound should be categorized as a DerivedLemma"
        );
        assert!(
            def.value_src.is_some(),
            "definitional_extension_sound should carry a constructive value term"
        );
    }

    /// EnvSound is now a FAITHFUL definition, not a bare `KEnv -> Type` axiom: it
    /// carries a constructive value term that unfolds to the real reachability
    /// witness `DefinitionalExtension KEnv.empty env`. This is the anti-masquerade
    /// pin — soundness means "reachable from empty by a valid extension chain", NOT
    /// a vacuous always-true predicate.
    #[test]
    fn test_env_sound_is_faithful_definition_not_axiom() {
        let spec = build_env_extensions_spec();
        let def = spec
            .definitions()
            .get("EnvSound")
            .expect("EnvSound should exist");
        assert!(
            !def.is_axiom,
            "EnvSound must no longer be an axiom — it carries a definitional body"
        );
        let value = def
            .value_src
            .as_ref()
            .expect("EnvSound should carry a constructive value term");
        assert!(
            value.contains("DefinitionalExtension") && value.contains("KEnv.empty"),
            "EnvSound must unfold to the DefinitionalExtension-from-empty reachability witness, got: {value}"
        );
        // EnvSound must elaborate and kernel-type-check as a real definition.
        spec.verify_definition("EnvSound")
            .expect("EnvSound should elaborate and type-check as a definition");
    }

    /// The two step lemmas are now DERIVED THEOREMS with constructive proof terms,
    /// not HelperAxioms. Each proof discharges one extension step via transitivity
    /// of the closure composed with the matching immediate-step constructor.
    #[test]
    fn test_step_preservation_lemmas_are_derived_not_axioms() {
        let spec = build_env_extensions_spec();
        for (helper, lifter) in [
            (
                "constant_extension_preserves_soundness",
                "DefinitionalExtension.const_",
            ),
            (
                "inductive_extension_preserves_soundness",
                "DefinitionalExtension.inductive_",
            ),
        ] {
            let def = spec
                .definitions()
                .get(helper)
                .unwrap_or_else(|| panic!("{helper} should exist"));
            assert!(
                !def.is_axiom,
                "{helper} must no longer be an axiom — it carries a proof term"
            );
            assert_eq!(
                def.category,
                AxiomCategory::DerivedLemma,
                "{helper} should be categorized as a DerivedLemma"
            );
            let value = def
                .value_src
                .as_ref()
                .unwrap_or_else(|| panic!("{helper} should carry a value term"));
            assert!(
                value.contains("DefinitionalExtension.trans") && value.contains(lifter),
                "{helper} proof must compose trans with {lifter}, got: {value}"
            );
            // The proof term elaborates and kernel-type-checks.
            spec.verify_definition(helper)
                .unwrap_or_else(|e| panic!("{helper} should type-check: {e:?}"));
        }
    }

    /// The promotion pipeline (the authoritative DerivedProved gate) kernel-checks
    /// each step lemma and PROMOTES it: with EnvSound a faithful definition and the
    /// proof resting only on the FoundationalRule extension constructors, the
    /// computed axiom_deps are empty and the status becomes DerivedProved.
    #[test]
    fn test_step_preservation_lemmas_promote_to_derived_proved() {
        for helper in [
            "constant_extension_preserves_soundness",
            "inductive_extension_preserves_soundness",
        ] {
            let mut spec = build_env_extensions_spec();
            let src = spec
                .definitions()
                .get(helper)
                .unwrap_or_else(|| panic!("{helper} should exist"))
                .value_src
                .clone()
                .unwrap_or_else(|| panic!("{helper} should carry a value term"));

            let attempt = crate::proofs::promote::promote_with_proof_term(&mut spec, helper, &src)
                .unwrap_or_else(|e| panic!("{helper} proof must type-check: {e:?}"));

            assert!(
                attempt.promoted,
                "{helper} must promote — its closure has no helper axioms: {attempt:?}"
            );
            assert_eq!(
                attempt.new_status,
                ProofStatus::DerivedProved,
                "{helper} must reach DerivedProved: {attempt:?}"
            );
            assert!(
                attempt.axiom_deps.is_empty(),
                "{helper} must have an empty helper-axiom closure: {:?}",
                attempt.axiom_deps
            );
        }
    }

    /// The consumer theorem now has an EMPTY helper-axiom closure in the static
    /// snapshot: EnvSound is a definition and both step lemmas are derived, so the
    /// whole soundness chain rests only on the trusted extension-judgment rules.
    /// It is carried at DerivedPending (the reducible-definition convention; the
    /// promotion pipeline performs the DerivedProved upgrade — see the promotion
    /// test below), but with no remaining axiom debt.
    #[test]
    fn test_definitional_extension_sound_has_no_helper_axiom_closure() {
        let spec = build_env_extensions_spec();
        let def = spec
            .definitions()
            .get("definitional_extension_sound")
            .expect("definitional_extension_sound should exist");

        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedPending,
            "definitional_extension_sound is carried DerivedPending in the static snapshot: {:?}",
            def.proof_status
        );
        assert!(
            def.axiom_deps.is_empty(),
            "definitional_extension_sound should have no helper-axiom closure: {:?}",
            def.axiom_deps
        );
        // It must NOT name the now-retired helpers/EnvSound as axiom debt.
        for retired in [
            "EnvSound",
            "constant_extension_preserves_soundness",
            "inductive_extension_preserves_soundness",
            "FreshDeclName",
            "StrictlyPositiveCtorDecls",
            "WellFormedCtorDecls",
        ] {
            assert!(
                !def.axiom_deps.contains(retired),
                "definitional_extension_sound must no longer carry {retired} as axiom debt: {:?}",
                def.axiom_deps
            );
        }
    }

    /// Promotion of the consumer kernel-checks its full recursor proof and promotes
    /// it: walking the proof's constants surfaces no HelperAxiom and no unproved
    /// DerivedLemma dependency, so the computed axiom_deps are empty.
    #[test]
    fn test_definitional_extension_sound_promotes_to_derived_proved() {
        let mut spec = build_env_extensions_spec();
        // Promote the step lemmas first so the consumer's DerivedLemma deps are
        // themselves DerivedProved (mirrors a full promotion pass).
        for helper in [
            "constant_extension_preserves_soundness",
            "inductive_extension_preserves_soundness",
        ] {
            let src = spec
                .definitions()
                .get(helper)
                .unwrap_or_else(|| panic!("{helper} should exist"))
                .value_src
                .clone()
                .unwrap_or_else(|| panic!("{helper} should carry a value term"));
            crate::proofs::promote::promote_with_proof_term(&mut spec, helper, &src)
                .unwrap_or_else(|e| panic!("{helper} should promote: {e:?}"));
        }

        let src = spec
            .definitions()
            .get("definitional_extension_sound")
            .expect("definitional_extension_sound should exist")
            .value_src
            .clone()
            .expect("definitional_extension_sound should carry a value term");

        let attempt = crate::proofs::promote::promote_with_proof_term(
            &mut spec,
            "definitional_extension_sound",
            &src,
        )
        .expect("the proof term type-checks, so promotion must not error");

        assert!(
            attempt.promoted,
            "definitional_extension_sound must promote to DerivedProved: {attempt:?}"
        );
        assert_eq!(
            attempt.new_status,
            ProofStatus::DerivedProved,
            "classification must be DerivedProved: {attempt:?}"
        );
        assert!(
            attempt.axiom_deps.is_empty(),
            "promotion-computed axiom_deps must be empty: {:?}",
            attempt.axiom_deps
        );
    }
}

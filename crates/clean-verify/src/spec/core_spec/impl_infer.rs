// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! `ImplInfer` — the layer-1 inference relation for the DEPLOYED kernel
//! (job C1 / migration step M3 of
//! `designs/2026-07-29-unified-implinfer-relation.md`).
//!
//! # The object of study
//!
//! `clean_kernel::TypeChecker::infer_type` in its **release** body —
//! `infer_type_fast_inner`, `crates/clean-kernel/src/tc/infer.rs:348-683`, 24
//! dispatch arms over 25 `ExprKind` constructors — under `infer_only = false`,
//! because that is the only mode a declaration is admitted through **on the
//! CHECKED path** (`env/decl_add.rs` reaches it via `infer_sort` / `check_type`,
//! which set the flag). Qualified deliberately: `add_decl_unchecked`
//! (`env/decl_add.rs:1128`) and `add_decl_structural` (`:1224`) admit without
//! running this body at all. Those are the paths the `// SOUNDNESS:` comment rule
//! and `data/unchecked_decl_ratchet.json` exist to bound; nothing here says
//! anything about them.
//!
//! # Two unmodelled release caches, named as residuals
//!
//! The release entry points consult two memo layers this relation does not model,
//! and a hit on either means the `next_id` in/out trace below is an
//! over-approximation of one concrete execution rather than a transcript of it:
//!
//! * the closed-term type cache, consulted only when the local context is empty
//!   (`tc/infer.rs:250-256`, `try_get_cached_type` at `:271`);
//! * the `Arc`-identity infer memo keyed on `(ptr, infer_only, ctx_len)`
//!   (`tc/infer.rs:323-344`).
//!
//! Neither can make the relation admit something the deployed body rejects — a
//! memo returns a type the same body computed earlier — but both mean "the arm
//! ran and threaded the counter" is not literally what happened. Modelling them
//! is Phase-B width.
//!
//! The debug and release bodies are NOT interchangeable, so the modelled
//! artifact is specifically the `not(debug_assertions)` configuration and nothing
//! here should be read as a statement about the debug body. In infer-only mode
//! the debug body is strictly stricter: certificate construction makes it infer
//! the App argument, the Lam domain and the Let type/value unconditionally, where
//! release guards each behind `!infer_only`. Consequence worth stating plainly:
//! every `cargo test` exercises the body this relation is NOT about.
//!
//! (The companion design doc lists as step M0 "fix the false docstring at
//! `infer.rs:82`". That is already DONE and must not be re-reported: the
//! docstring at `tc/infer.rs:83-94` now states the contract correctly — it scopes
//! "identical" to check mode, documents the infer-only divergence, and notes
//! debug "never accepts more". It landed in `cfbf8c9e8`, an ancestor of this
//! lane. An earlier version of this module doc contradicted that docstring and
//! was wrong to.)
//!
//! # Coverage — stated as a fraction, never rounded up
//!
//! * **9 constructors**, one per successful release dispatch arm:
//!   `sort`, `fvar`, `const`, `app`, `lam`, `pi`, `let_`, `lit`, `mdata`.
//! * **1 refutation rule**, `impl_infer_bvar_rejects`: the release `BVar` arm
//!   returns `Err(UnboundVariable)` unconditionally (`tc/infer.rs:350`), so an
//!   `ImplInfer` derivation at a `bvar` is uninhabited — and that is *proved*
//!   here, not assumed.
//! * So **10 of 24** release dispatch arms carry a rule.
//! * **13 more** are discharged by the mode-gate side lemma
//!   (`impl_infer_mode_gate`): under `mode = Constructive` (the `#[default]`)
//!   every extension arm hits an unconditional gate and returns
//!   `Err(ModeRequired)` *before any recursion*.
//! * **1 is excluded outright**, named individually: `Proj`
//!   (`tc/infer.rs:651`). It calls `is_prop`, which calls
//!   `infer_type_infer_only` — a mode switch INSIDE the arm — plus a
//!   `proj_type_cache` keyed on a rebuilt node and a constructor-telescope walk.
//!
//! **23 of 24.**
//!
//! # Why this and not `KernelInferAccepts`
//!
//! `KernelInferAccepts` (model B) recursively accepts the raw de Bruijn body of
//! a `Lam` *in the same state*, never opening the binder — so it **cannot
//! represent `λ(x : Prop). x` being accepted**, though both the deployed kernel
//! and the layer-2 models that HAVE a variable rule (`KernelInfers`,
//! `TypingCtxConv`) accept it — NOT the degenerate env-free `Typing`/`has_type`,
//! which has no bvar rule at all (`typing_def_eq.rs:119-124`) and whose
//! inhabitants are bvar-free (`beta_bd_sn.rs:315-319`). Its `const` arm asserts a layer-2 typing
//! judgment (`has_type (const n us) T`) instead of performing the layer-1
//! *operations*, and `const_untypable` refutes that conclusion in valid states.
//! Both defects are one mistake: mixing the layers.
//!
//! `implinfer_lam_identity_witness` (next stage) is the direct answer: the exact
//! term B cannot represent, derived here from constructors alone.
//!
//! # The operational boundary
//!
//! `ImplWhnfTo` and `ImplIsLe` are *separately-modelled calls* (vacuity-firewall
//! rule 3): they are real inductives with operational content, NOT parameters
//! and NOT axioms, so the firewall can walk their constructor fields. Each owes
//! an independent soundness theorem against the layer-2 `DefEq` under the
//! representation relation — that is the C4 bridge job, not this one.
//!
//! ZERO new axioms: every declaration is an inductive (census-neutral) or a
//! valued definition.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

impl Specification {
    /// M3: the operational boundary relations, the `ImplInfer` relation itself,
    /// and the `bvar` refutation.
    pub(super) fn add_impl_infer(&mut self) -> Result<(), SpecError> {
        self.add_impl_infer_boundary()?;
        self.add_impl_infer_relation()?;
        self.add_impl_infer_refutation()?;
        self.add_impl_infer_monotonicity()?;
        Ok(())
    }

    /// `next_id` monotonicity — the freshness discipline, proved.
    ///
    /// Production's `LocalContext.next_id` is incremented on every push
    /// (`tc/local_context.rs:81,111`) and NEVER rewound: `ctx_pop` removes the
    /// declaration but `used_ids` retains the id, and `push` asserts an id is
    /// never reused (`:86-89`). The relation's in/out indices must reflect that,
    /// and this theorem is what makes it a fact about the relation rather than a
    /// property of how the arms happen to be written.
    ///
    /// It is also what a freshness argument downstream actually needs: at a
    /// binder the arm names its fresh id as the CURRENT counter and hands the
    /// successor to the body, so `n <= m` on every sub-derivation is exactly the
    /// statement that no later arm can mint an id an earlier one already used.
    fn add_impl_infer_monotonicity(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "impl_infer_next_id_monotone".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType ImplConstInfo) (lps : ListType Name) ",
                "(n : Nat) (G : LCtx) (e : ImplExpr) (T : ImplExpr) (m : Nat), ",
                "ImplInfer tenv lps n G e T m -> Le n m"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType ImplConstInfo) (lps : ListType Name) ",
                    "(n : Nat) (G : LCtx) (e : ImplExpr) (T : ImplExpr) (m : Nat) ",
                    "(h : ImplInfer tenv lps n G e T m) => ",
                    "ImplInfer.rec tenv lps ",
                    "(fun (n2 : Nat) (G2 : LCtx) (e2 : ImplExpr) (T2 : ImplExpr) (m2 : Nat) ",
                    "(_h : ImplInfer tenv lps n2 G2 e2 T2 m2) => Le n2 m2) ",
                    // sort / fvar / const / lit: the counter is untouched.
                    "(fun (sn : Nat) (sG : LCtx) (sl : Level) ",
                    "(shl : Eq Bool (level_params_ok lps sl) Bool.true) => Le.refl sn) ",
                    "(fun (vn : Nat) (vG : LCtx) (vx : Nat) (vA : ImplExpr) ",
                    "(vlk : Eq (OptionType ImplExpr) (lctx_lookup vG vx) (OptionType.some ImplExpr vA)) => Le.refl vn) ",
                    "(fun (cn : Nat) (cG : LCtx) (cnm : Name) (cus : ListType Level) (cci : ImplConstInfo) ",
                    "(cget : Eq (OptionType ImplConstInfo) (tenv cnm) (OptionType.some ImplConstInfo cci)) ",
                    "(car : Eq Nat (name_list_len (impl_const_lps cci)) (level_list_len cus)) ",
                    "(clv : Eq Bool (impl_levels_ok lps cus) Bool.true) ",
                    "(cuf : Eq Bool (impl_const_unsafe cci) Bool.false) ",
                    "(cpf : Eq Bool (impl_const_partial cci) Bool.false) => Le.refl cn) ",
                    // app: two sub-derivations in sequence, n -> n1 -> n2.
                    "(fun (an : Nat) (an1 : Nat) (an2 : Nat) (aG : LCtx) (af : ImplExpr) (aa : ImplExpr) ",
                    "(aF : ImplExpr) (abd : BinderData) (aA : ImplExpr) (aB : ImplExpr) (aA2 : ImplExpr) ",
                    "(ahf : ImplInfer tenv lps an aG af aF an1) ",
                    "(ahw : ImplWhnfTo aF (ImplExpr.pi abd aA aB)) ",
                    "(aha : ImplInfer tenv lps an1 aG aa aA2 an2) ",
                    "(ahle : ImplIsLe aA2 aA) ",
                    "(aihf : Le an an1) (aiha : Le an1 an2) => ",
                    "le_trans an an1 an2 aihf aiha) ",
                    // lam: n -> n1 (domain), then the binder consumes n1 and the
                    // body runs from succ n1 -> n2. Le n1 (succ n1) bridges them.
                    "(fun (ln : Nat) (ln1 : Nat) (ln2 : Nat) (lG : LCtx) (lbd : BinderData) ",
                    "(lA : ImplExpr) (lb : ImplExpr) (lS : ImplExpr) (ll : Level) (lbt : ImplExpr) ",
                    "(lhA : ImplInfer tenv lps ln lG lA lS ln1) ",
                    "(lhS : ImplWhnfTo lS (ImplExpr.sort ll)) ",
                    "(lhb : ImplInfer tenv lps (Nat.succ ln1) (LCtx.snoc lG (LocalDecl.mk ln1 lA (OptionType.none ImplExpr) lbd)) (impl_open lb ln1) lbt ln2) ",
                    "(lihA : Le ln ln1) (lihb : Le (Nat.succ ln1) ln2) => ",
                    "le_trans ln ln1 ln2 lihA ",
                    "(le_trans ln1 (Nat.succ ln1) ln2 (Le.step ln1 ln1 (Le.refl ln1)) lihb)) ",
                    // pi: identical counter discipline to lam.
                    "(fun (pn : Nat) (pn1 : Nat) (pn2 : Nat) (pG : LCtx) (pbd : BinderData) ",
                    "(pA : ImplExpr) (pb : ImplExpr) (pS1 : ImplExpr) (pS2 : ImplExpr) (pl1 : Level) (pl2 : Level) ",
                    "(phA : ImplInfer tenv lps pn pG pA pS1 pn1) ",
                    "(phS1 : ImplWhnfTo pS1 (ImplExpr.sort pl1)) ",
                    "(phb : ImplInfer tenv lps (Nat.succ pn1) (LCtx.snoc pG (LocalDecl.mk pn1 pA (OptionType.none ImplExpr) pbd)) (impl_open pb pn1) pS2 pn2) ",
                    "(phS2 : ImplWhnfTo pS2 (ImplExpr.sort pl2)) ",
                    "(pihA : Le pn pn1) (pihb : Le (Nat.succ pn1) pn2) => ",
                    "le_trans pn pn1 pn2 pihA ",
                    "(le_trans pn1 (Nat.succ pn1) pn2 (Le.step pn1 pn1 (Le.refl pn1)) pihb)) ",
                    // let_: three sub-derivations, n -> n1 -> n2, then the let
                    // binder consumes n2 and the body runs succ n2 -> n3.
                    "(fun (zn : Nat) (zn1 : Nat) (zn2 : Nat) (zn3 : Nat) (zG : LCtx) (znm : Name) ",
                    "(zty : ImplExpr) (zv : ImplExpr) (zb : ImplExpr) (zS : ImplExpr) (zl : Level) ",
                    "(zTv : ImplExpr) (zbt : ImplExpr) ",
                    "(zhty : ImplInfer tenv lps zn zG zty zS zn1) ",
                    "(zhS : ImplWhnfTo zS (ImplExpr.sort zl)) ",
                    "(zhv : ImplInfer tenv lps zn1 zG zv zTv zn2) ",
                    "(zhle : ImplIsLe zTv zty) ",
                    "(zhb : ImplInfer tenv lps (Nat.succ zn2) (LCtx.snoc zG (LocalDecl.mk zn2 zty (OptionType.some ImplExpr zv) (BinderData.mk BinderInfo.default Multiplicity.many))) (impl_open zb zn2) zbt zn3) ",
                    "(zihty : Le zn zn1) (zihv : Le zn1 zn2) (zihb : Le (Nat.succ zn2) zn3) => ",
                    "le_trans zn zn2 zn3 (le_trans zn zn1 zn2 zihty zihv) ",
                    "(le_trans zn2 (Nat.succ zn2) zn3 (Le.step zn2 zn2 (Le.refl zn2)) zihb)) ",
                    "(fun (in2 : Nat) (iG : LCtx) (ilt : ImplLit) => Le.refl in2) ",
                    // mdata: transparent, so the body's own bound is the answer.
                    "(fun (mn : Nat) (mn1 : Nat) (mG : LCtx) (me : ImplExpr) (mT : ImplExpr) ",
                    "(mh : ImplInfer tenv lps mn mG me mT mn1) (mih : Le mn mn1) => mih) ",
                    "n G e T m h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "next_id MONOTONICITY: every ImplInfer derivation runs the freshness counter ",
                "forward, never backward. Production's LocalContext.next_id is incremented on ",
                "every push (tc/local_context.rs:81,111) and NEVER rewound — ctx_pop drops the ",
                "declaration but used_ids retains the id, and push asserts an id is never reused ",
                "(:86-89). Proved by ImplInfer.rec: the four non-recursive arms leave the counter ",
                "alone (Le.refl), app/let_ chain their sub-derivations with le_trans, and the ",
                "binder arms bridge n1 to succ n1 with Le.step before chaining. This is the ",
                "statement a downstream freshness argument needs: no arm can mint an FVarId an ",
                "earlier arm already used, which is what lets the design avoid cofinite ",
                "quantification entirely. Zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplInfer".to_string(),
                "ImplInfer.rec".to_string(),
                "Le".to_string(),
                "Le.refl".to_string(),
                "Le.step".to_string(),
                "le_trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })
    }

    /// The two separately-modelled operational calls the release body makes
    /// from inside its arms, plus the literal-arm result table.
    fn add_impl_infer_boundary(&mut self) -> Result<(), SpecError> {
        // ImplWhnfTo e r : "whnf_impl reduces e to r".
        //
        // The release App/Lam/Pi/Let arms all call `self.whnf_impl(..)` and then
        // MATCH on the reduct's head (tc/infer.rs:438,521,555,573,594). Modelling it
        // as a relation — rather than as a total function — is what keeps the
        // arm faithful: production inspects the reduct, it does not assume one.
        //
        // HONEST RESIDUAL, named: this covers the ENV-FREE reductions only —
        // beta, zeta, and the mdata passthrough, plus UNRESTRICTED reflexivity
        // (`done` holds at every ImplExpr, not only at whnf-normal ones — the
        // relation over-approximates whnf and is refined by its soundness theorem). Delta (constant unfolding), iota (recursor
        // reduction), projection reduction and eta all need the environment and
        // are Phase-B width, not part of the C1 skeleton. A derivation that
        // needs them simply cannot be built here; nothing false is admitted.
        self.add_inductive(
            concat!(
                "inductive ImplWhnfTo : ImplExpr -> ImplExpr -> Type\n",
                "| done : forall (e : ImplExpr), ImplWhnfTo e e\n",
                "| beta : forall (bd : BinderData) (A : ImplExpr) (b : ImplExpr) (a : ImplExpr) (r : ImplExpr), ImplWhnfTo (impl_instantiate b a) r -> ImplWhnfTo (ImplExpr.app (ImplExpr.lam bd A b) a) r\n",
                "| zeta : forall (nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ImplExpr) (r : ImplExpr), ImplWhnfTo (impl_instantiate b v) r -> ImplWhnfTo (ImplExpr.let_ nm ty v b) r\n",
                "| mdataStep : forall (e : ImplExpr) (r : ImplExpr), ImplWhnfTo e r -> ImplWhnfTo (ImplExpr.mdata e) r"
            ),
            "Weak-head reduction on the layer-1 syntax — the `whnf_impl` call the \
             release App/Lam/Pi/Let arms make before matching on the reduct's head \
             (tc/infer.rs:438,521,555,573,594). The list includes :573, the pi arm's SECOND ensure_sort, which is \
             why the pi rule carries two ImplWhnfTo premises. A RELATION, not a \
             function: production \
             inspects the reduct rather than assuming one. `done` is UNRESTRICTED \
             reflexivity — it holds at every ImplExpr, not only at whnf-normal ones, \
             so the relation over-approximates whnf and is refined by its \
             soundness theorem rather than by its own shape. Covers the env-free \
             fragment (done/beta/zeta/mdata); delta, iota, proj and eta need the \
             environment and are Phase-B width — named as a residual, never \
             assumed. Separately-modelled operational call per vacuity-firewall \
             rule 3: it owes an independent ImplWhnfTo -> DefEq soundness theorem \
             under the representation relation (the C4 bridge job). ZERO new axioms.",
        )?;

        // ImplIsLe a b : "is_le(a, b)" — the CUMULATIVE subtyping check the
        // release App-argument and Let-value ascription points perform
        // (tc/infer.rs:474, :617). `is_le` == `is_def_eq` off the Coq
        // cumulative lane.
        //
        // HONEST RESIDUAL, named: this is the reflexive, whnf-closed fragment.
        // Congruence, eta, proof irrelevance and universe cumulativity are NOT
        // here. As with ImplWhnfTo, the relation admits nothing false — it
        // simply cannot yet witness every acceptance the deployed checker makes.
        self.add_inductive(
            concat!(
                "inductive ImplIsLe : ImplExpr -> ImplExpr -> Type\n",
                "| refl : forall (e : ImplExpr), ImplIsLe e e\n",
                "| whnfL : forall (a : ImplExpr) (b : ImplExpr) (r : ImplExpr), ImplWhnfTo a r -> ImplIsLe r b -> ImplIsLe a b\n",
                "| whnfR : forall (a : ImplExpr) (b : ImplExpr) (r : ImplExpr), ImplWhnfTo b r -> ImplIsLe a r -> ImplIsLe a b"
            ),
            "The cumulative-subtyping check `is_le` the release App-argument \
             (tc/infer.rs:474) and Let-value (:617) ascription points perform; \
             `is_le` == `is_def_eq` unless the Coq cumulative lane is enabled. \
             Modelled here as its reflexive, whnf-closed fragment — congruence, \
             eta, proof irrelevance and universe cumulativity are Phase-B width and \
             are NAMED as a residual rather than assumed. Separately-modelled \
             operational call per vacuity-firewall rule 3; owes an independent \
             ImplIsLe -> DefEq soundness theorem (the C4 bridge job). ZERO new axioms.",
        )?;

        // The two constant names the Lit arm returns. The kernel returns
        // `Expr::const_(NAME_NAT, vec![])` / `NAME_STRING` with ZERO environment
        // validation (tc/infer.rs:647-650) — it does not check that `Nat` or
        // `String` is even declared. Modelled exactly that way: two distinct
        // interned names, no env premise.
        self.add_recursive_def(
            r"def impl_name_nat : Name := Name.str Name.anonymous Nat.zero",
            "The interned name `Nat` the release Lit arm returns for Literal::Nat \
             (NAME_NAT, tc/infer.rs:648). The spec's Name encodes string segments \
             as Nat ids; only its DISTINCTNESS from impl_name_string is load-bearing.",
        )?;
        self.add_recursive_def(
            r"def impl_name_string : Name := Name.str Name.anonymous (Nat.succ Nat.zero)",
            "The interned name `String` the release Lit arm returns for \
             Literal::String (NAME_STRING, tc/infer.rs:649).",
        )?;
        self.add_recursive_def(
            r"def impl_lit_type (l : ImplLit) : ImplExpr := match l with
| ImplLit.natVal k => ImplExpr.const impl_name_nat (ListType.nil Level)
| ImplLit.strVal k => ImplExpr.const impl_name_string (ListType.nil Level)",
            "The release Lit arm's result table (tc/infer.rs:647-650): Nat literals \
             get `const Nat []`, String literals get `const String []`. The literal \
             VALUE is discarded and there is ZERO environment validation — modelled \
             faithfully, including the absence of any env premise on the lit rule.",
        )?;

        // A one-constructor Type used as the "not refuted" alternative of the
        // refutation motive below. `Empty` and the alternative must live in the
        // same universe for the motive's match to be well-formed, so the spec's
        // Prop-valued `Eq` cannot serve.
        self.add_inductive(
            r"inductive ImplUnit : Type
| mk : ImplUnit",
            "Single-inhabitant Type. Universe adapter for the ImplNotBVar \
             refutation motive, whose ImplExpr.rec must return Type in EVERY arm \
             while one arm is Empty (Type) — the spec's Eq is Prop-valued and \
             cannot be the other alternative.",
        )?;

        Ok(())
    }

    /// The relation itself: 9 constructors, one per successful release arm.
    fn add_impl_infer_relation(&mut self) -> Result<(), SpecError> {
        // ImplInfer tenv lps n G e T m
        //   tenv : the constant environment (`env.get_const`)
        //   lps  : the declaration's DECLARED level params (`check_level`'s basis)
        //   n    : next_id IN     G : the local context     e : the input node
        //   T    : the inferred type            m : next_id OUT
        //
        // The in/out `next_id` indices are what make freshness decidable numeric
        // arithmetic instead of cofinite quantification: production's
        // `LocalContext.next_id` is incremented on every push and NEVER rewound
        // (tc/local_context.rs:81,111; `used_ids` asserts an id is never reused,
        // :86-89), so a binder arm can simply NAME its fresh id as the current
        // counter value and hand the successor to its body.
        //
        // Every premise below is an OPERATION the deployed arm performs, in the
        // order it performs it. Nothing here asserts a typing judgment — that is
        // the layer-2 job, and asserting it here is precisely model B's defect.
        self.add_inductive(
            concat!(
                "inductive ImplInfer (tenv : Name -> OptionType ImplConstInfo) (lps : ListType Name) : Nat -> LCtx -> ImplExpr -> ImplExpr -> Nat -> Type\n",
                // ── sort (tc/infer.rs:360-370) ──────────────────────────────
                // check_level in check mode, then Sort(succ l). No recursion,
                // no context change, next_id untouched.
                "| sort : forall (n : Nat) (G : LCtx) (l : Level), Eq Bool (level_params_ok lps l) Bool.true -> ImplInfer tenv lps n G (ImplExpr.sort l) (ImplExpr.sort (Level.succ l)) n\n",
                // ── fvar (tc/infer.rs:351-359) ──────────────────────────────
                // Context lookup by FVarId, returning the stored type UNLIFTED.
                // This is where layer 1 visibly differs from KernelInfers.bvar /
                // TypingCtxConv.var, both of which apply lift_at A 0 (succ i).
                "| fvar : forall (n : Nat) (G : LCtx) (x : Nat) (A : ImplExpr), Eq (OptionType ImplExpr) (lctx_lookup G x) (OptionType.some ImplExpr A) -> ImplInfer tenv lps n G (ImplExpr.fvar x) A n\n",
                // ── const (tc/infer.rs:371-424) ─────────────────────────────
                // FIVE operations, all present: get_const, level-arity equality,
                // check_level per level, the unsafe gate, the partial gate; the
                // result is instantiate_level_params_direct. Model B's const arm
                // models ZERO of these.
                "| const : forall (n : Nat) (G : LCtx) (nm : Name) (us : ListType Level) (ci : ImplConstInfo), Eq (OptionType ImplConstInfo) (tenv nm) (OptionType.some ImplConstInfo ci) -> Eq Nat (name_list_len (impl_const_lps ci)) (level_list_len us) -> Eq Bool (impl_levels_ok lps us) Bool.true -> Eq Bool (impl_const_unsafe ci) Bool.false -> Eq Bool (impl_const_partial ci) Bool.false -> ImplInfer tenv lps n G (ImplExpr.const nm us) (impl_inst_levels (impl_const_lps ci) us (impl_const_type ci)) n\n",
                // ── app (tc/infer.rs:425-508) ───────────────────────────────
                // infer f; whnf its type to a Pi; infer the argument; is_le the
                // argument's type against the domain; result instantiate B a.
                // next_id threads n -> n1 (function) -> n2 (argument).
                "| app : forall (n : Nat) (n1 : Nat) (n2 : Nat) (G : LCtx) (f : ImplExpr) (a : ImplExpr) (F : ImplExpr) (bd : BinderData) (A : ImplExpr) (B : ImplExpr) (A2 : ImplExpr), ImplInfer tenv lps n G f F n1 -> ImplWhnfTo F (ImplExpr.pi bd A B) -> ImplInfer tenv lps n1 G a A2 n2 -> ImplIsLe A2 A -> ImplInfer tenv lps n G (ImplExpr.app f a) (impl_instantiate B a) n2\n",
                // ── lam (tc/infer.rs:509-549) ───────────────────────────────
                // Check the domain is a sort; mint fresh id n1; push (n1, A, no
                // value, bd); OPEN the body to FVar(n1); infer; ABSTRACT n1 back
                // out; conclude Pi bd A (abstract bt n1). This is the arm model B
                // cannot express: it recurses on the RAW de Bruijn body.
                "| lam : forall (n : Nat) (n1 : Nat) (n2 : Nat) (G : LCtx) (bd : BinderData) (A : ImplExpr) (b : ImplExpr) (S : ImplExpr) (l : Level) (bt : ImplExpr), ImplInfer tenv lps n G A S n1 -> ImplWhnfTo S (ImplExpr.sort l) -> ImplInfer tenv lps (Nat.succ n1) (LCtx.snoc G (LocalDecl.mk n1 A (OptionType.none ImplExpr) bd)) (impl_open b n1) bt n2 -> ImplInfer tenv lps n G (ImplExpr.lam bd A b) (ImplExpr.pi bd A (impl_abstract_fvar bt n1)) n2\n",
                // ── pi (tc/infer.rs:550-583) ────────────────────────────────
                // Identical binder discipline to lam, but BOTH sorts are whnf'd
                // and required, and there is NO infer_only guard — Pi always
                // checks. Result Sort (imax l1 l2).
                "| pi : forall (n : Nat) (n1 : Nat) (n2 : Nat) (G : LCtx) (bd : BinderData) (A : ImplExpr) (b : ImplExpr) (S1 : ImplExpr) (S2 : ImplExpr) (l1 : Level) (l2 : Level), ImplInfer tenv lps n G A S1 n1 -> ImplWhnfTo S1 (ImplExpr.sort l1) -> ImplInfer tenv lps (Nat.succ n1) (LCtx.snoc G (LocalDecl.mk n1 A (OptionType.none ImplExpr) bd)) (impl_open b n1) S2 n2 -> ImplWhnfTo S2 (ImplExpr.sort l2) -> ImplInfer tenv lps n G (ImplExpr.pi bd A b) (ImplExpr.sort (Level.imax l1 l2)) n2\n",
                // ── let_ (tc/infer.rs:584-646) ──────────────────────────────
                // Annotation inferred and whnf'd to a sort; value inferred and
                // is_le-checked against the annotation; body opened under a LET
                // decl (value present, BinderInfo::Default / Multiplicity::Many
                // — ctx_push_let at tc/config.rs:48, reaching LocalContext::push_let at
             // tc/local_context.rs:109-128); the result is
                // subst_fvar, i.e. ZETA DIRECTLY, not `instantiate` and not an
                // abstract+instantiate round trip (tc/infer.rs:641-645).
                "| let_ : forall (n : Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (G : LCtx) (nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ImplExpr) (S : ImplExpr) (l : Level) (Tv : ImplExpr) (bt : ImplExpr), ImplInfer tenv lps n G ty S n1 -> ImplWhnfTo S (ImplExpr.sort l) -> ImplInfer tenv lps n1 G v Tv n2 -> ImplIsLe Tv ty -> ImplInfer tenv lps (Nat.succ n2) (LCtx.snoc G (LocalDecl.mk n2 ty (OptionType.some ImplExpr v) (BinderData.mk BinderInfo.default Multiplicity.many))) (impl_open b n2) bt n3 -> ImplInfer tenv lps n G (ImplExpr.let_ nm ty v b) (impl_subst_fvar bt n2 v) n3\n",
                // ── lit (tc/infer.rs:647-650) ───────────────────────────────
                // A fixed constant per literal kind, ZERO env validation.
                "| lit : forall (n : Nat) (G : LCtx) (lt : ImplLit), ImplInfer tenv lps n G (ImplExpr.lit lt) (impl_lit_type lt) n\n",
                // ── mdata (tc/infer.rs:657-663) ─────────────────────────────
                // Fully transparent passthrough: same type, same next_id flow.
                "| mdata : forall (n : Nat) (n1 : Nat) (G : LCtx) (e : ImplExpr) (T : ImplExpr), ImplInfer tenv lps n G e T n1 -> ImplInfer tenv lps n G (ImplExpr.mdata e) T n1"
            ),
            "ImplInfer tenv lps n G e T m: the layer-1 inference relation for the \
             DEPLOYED release body infer_type_fast_inner (tc/infer.rs:348-683) under \
             infer_only=false — the only mode a declaration is admitted through. \
             Nine constructors, one per successful dispatch arm (sort, fvar, const, \
             app, lam, pi, let_, lit, mdata); the BVar arm is a REFUTATION \
             (impl_infer_bvar_rejects) because production errors on it \
             unconditionally. Indices thread LocalContext.next_id IN and OUT, which \
             is what makes binder freshness decidable arithmetic instead of \
             cofinite quantification. Every premise is an OPERATION the arm \
             performs, in order — env lookup, arity, check_level, safety gates, \
             whnf, is_le, open/abstract, zeta — and NO premise asserts a typing \
             judgment (asserting one is exactly KernelInferAccepts' defect). \
             Coverage 23/24: 10 arms carry a rule, 13 are mode-gated, Proj is \
             excluded outright. ZERO new axioms (Inductive/Constructor/Recursor).",
        )?;

        Ok(())
    }

    /// The `bvar` refutation — the 10th modelled arm, proved rather than assumed.
    fn add_impl_infer_refutation(&mut self) -> Result<(), SpecError> {
        // ImplNotBVar: a semireducible per-shape family. Registered through the
        // REDUCIBLE path: plain add_definition registers non-Prop-valued defs as
        // Declaration::Opaque, which would block the iota unfolding the
        // refutation rides on (the InferInversionAt / not_lt_zero_goal precedent).
        //
        // At a bvar it reduces to Empty; at every other head to ImplUnit. Since
        // no ImplInfer constructor concludes at a bvar head, every minor of the
        // recursion below has goal ImplUnit and is discharged by ImplUnit.mk —
        // and the eliminated derivation's own index is `bvar i`, so the RESULT
        // type reduces to Empty. No injectivity or discriminator plumbing.
        self.add_definition_reducible(SpecDefinition {
            name: "ImplNotBVar".to_string(),
            type_src: "ImplExpr -> Type".to_string(),
            value_src: Some(
                concat!(
                    "fun (x : ImplExpr) => ",
                    "ImplExpr.rec (fun (_ : ImplExpr) => Type) ",
                    // bvar — the ONLY Empty arm
                    "(fun (i : Nat) => Empty) ",
                    // fvar
                    "(fun (y : Nat) => ImplUnit) ",
                    // sort
                    "(fun (l : Level) => ImplUnit) ",
                    // const
                    "(fun (nm : Name) (us : ListType Level) => ImplUnit) ",
                    // app (2 recursive fields -> 2 IHs)
                    "(fun (f : ImplExpr) (a : ImplExpr) (rf : Type) (ra : Type) => ImplUnit) ",
                    // lam (binder data + 2 recursive fields)
                    "(fun (bd : BinderData) (ty : ImplExpr) (b : ImplExpr) (rt : Type) (rb : Type) => ImplUnit) ",
                    // pi
                    "(fun (bd : BinderData) (ty : ImplExpr) (b : ImplExpr) (rt : Type) (rb : Type) => ImplUnit) ",
                    // let_ (name + 3 recursive fields)
                    "(fun (nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ImplExpr) (rt : Type) (rv : Type) (rb : Type) => ImplUnit) ",
                    // lit
                    "(fun (lt : ImplLit) => ImplUnit) ",
                    // mdata (1 recursive field)
                    "(fun (inner : ImplExpr) (ri : Type) => ImplUnit) ",
                    "x"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Semireducible per-shape family for the bvar refutation: ImplNotBVar x ",
                "reduces (ImplExpr.rec on x) to Empty at a bvar and to ImplUnit at every ",
                "other head. Used as the ImplInfer.rec motive so index unification happens ",
                "by REDUCTION rather than injectivity plumbing — the InferInversionAt ",
                "precedent. ZERO axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplExpr.rec".to_string(),
                "ImplUnit".to_string(),
                "Empty".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // impl_infer_bvar_rejects: the release BVar arm is
        //   ExprKind::BVar(idx) => Err(TypeError::UnboundVariable(*idx))
        // (tc/infer.rs:350) — unconditional, before any other work. So no
        // ImplInfer derivation can conclude at a bvar, and this PROVES it from
        // the constructor set rather than assuming a discrimination axiom.
        //
        // ImplInfer.rec shape: params (tenv, lps), then the motive over the five
        // indices plus the derivation, then nine minors in declaration order
        // (each binding all constructor arguments in order, then the IHs for its
        // recursive fields in field order), then the indices and the major.
        self.add_definition(SpecDefinition {
            name: "impl_infer_bvar_rejects".to_string(),
            type_src: concat!(
                "forall (tenv : Name -> OptionType ImplConstInfo) (lps : ListType Name) ",
                "(n : Nat) (G : LCtx) (i : Nat) (T : ImplExpr) (m : Nat), ",
                "ImplInfer tenv lps n G (ImplExpr.bvar i) T m -> Empty"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (tenv : Name -> OptionType ImplConstInfo) (lps : ListType Name) ",
                    "(n : Nat) (G : LCtx) (i : Nat) (T : ImplExpr) (m : Nat) ",
                    "(h : ImplInfer tenv lps n G (ImplExpr.bvar i) T m) => ",
                    "ImplInfer.rec tenv lps ",
                    "(fun (n2 : Nat) (G2 : LCtx) (e2 : ImplExpr) (T2 : ImplExpr) (m2 : Nat) ",
                    "(_h : ImplInfer tenv lps n2 G2 e2 T2 m2) => ImplNotBVar e2) ",
                    // sort: 4 args, 0 IH
                    "(fun (sn : Nat) (sG : LCtx) (sl : Level) ",
                    "(shl : Eq Bool (level_params_ok lps sl) Bool.true) => ImplUnit.mk) ",
                    // fvar: 5 args, 0 IH
                    "(fun (vn : Nat) (vG : LCtx) (vx : Nat) (vA : ImplExpr) ",
                    "(vlk : Eq (OptionType ImplExpr) (lctx_lookup vG vx) (OptionType.some ImplExpr vA)) => ImplUnit.mk) ",
                    // const: 10 args, 0 IH
                    "(fun (cn : Nat) (cG : LCtx) (cnm : Name) (cus : ListType Level) (cci : ImplConstInfo) ",
                    "(cget : Eq (OptionType ImplConstInfo) (tenv cnm) (OptionType.some ImplConstInfo cci)) ",
                    "(car : Eq Nat (name_list_len (impl_const_lps cci)) (level_list_len cus)) ",
                    "(clv : Eq Bool (impl_levels_ok lps cus) Bool.true) ",
                    "(cuf : Eq Bool (impl_const_unsafe cci) Bool.false) ",
                    "(cpf : Eq Bool (impl_const_partial cci) Bool.false) => ImplUnit.mk) ",
                    // app: 15 args, 2 IHs
                    "(fun (an : Nat) (an1 : Nat) (an2 : Nat) (aG : LCtx) (af : ImplExpr) (aa : ImplExpr) ",
                    "(aF : ImplExpr) (abd : BinderData) (aA : ImplExpr) (aB : ImplExpr) (aA2 : ImplExpr) ",
                    "(ahf : ImplInfer tenv lps an aG af aF an1) ",
                    "(ahw : ImplWhnfTo aF (ImplExpr.pi abd aA aB)) ",
                    "(aha : ImplInfer tenv lps an1 aG aa aA2 an2) ",
                    "(ahle : ImplIsLe aA2 aA) ",
                    "(aihf : ImplNotBVar af) (aiha : ImplNotBVar aa) => ImplUnit.mk) ",
                    // lam: 13 args, 2 IHs
                    "(fun (ln : Nat) (ln1 : Nat) (ln2 : Nat) (lG : LCtx) (lbd : BinderData) ",
                    "(lA : ImplExpr) (lb : ImplExpr) (lS : ImplExpr) (ll : Level) (lbt : ImplExpr) ",
                    "(lhA : ImplInfer tenv lps ln lG lA lS ln1) ",
                    "(lhS : ImplWhnfTo lS (ImplExpr.sort ll)) ",
                    "(lhb : ImplInfer tenv lps (Nat.succ ln1) (LCtx.snoc lG (LocalDecl.mk ln1 lA (OptionType.none ImplExpr) lbd)) (impl_open lb ln1) lbt ln2) ",
                    "(lihA : ImplNotBVar lA) (lihb : ImplNotBVar (impl_open lb ln1)) => ImplUnit.mk) ",
                    // pi: 15 args, 2 IHs
                    "(fun (pn : Nat) (pn1 : Nat) (pn2 : Nat) (pG : LCtx) (pbd : BinderData) ",
                    "(pA : ImplExpr) (pb : ImplExpr) (pS1 : ImplExpr) (pS2 : ImplExpr) (pl1 : Level) (pl2 : Level) ",
                    "(phA : ImplInfer tenv lps pn pG pA pS1 pn1) ",
                    "(phS1 : ImplWhnfTo pS1 (ImplExpr.sort pl1)) ",
                    "(phb : ImplInfer tenv lps (Nat.succ pn1) (LCtx.snoc pG (LocalDecl.mk pn1 pA (OptionType.none ImplExpr) pbd)) (impl_open pb pn1) pS2 pn2) ",
                    "(phS2 : ImplWhnfTo pS2 (ImplExpr.sort pl2)) ",
                    "(pihA : ImplNotBVar pA) (pihb : ImplNotBVar (impl_open pb pn1)) => ImplUnit.mk) ",
                    // let_: 18 args, 3 IHs
                    "(fun (zn : Nat) (zn1 : Nat) (zn2 : Nat) (zn3 : Nat) (zG : LCtx) (znm : Name) ",
                    "(zty : ImplExpr) (zv : ImplExpr) (zb : ImplExpr) (zS : ImplExpr) (zl : Level) ",
                    "(zTv : ImplExpr) (zbt : ImplExpr) ",
                    "(zhty : ImplInfer tenv lps zn zG zty zS zn1) ",
                    "(zhS : ImplWhnfTo zS (ImplExpr.sort zl)) ",
                    "(zhv : ImplInfer tenv lps zn1 zG zv zTv zn2) ",
                    "(zhle : ImplIsLe zTv zty) ",
                    "(zhb : ImplInfer tenv lps (Nat.succ zn2) (LCtx.snoc zG (LocalDecl.mk zn2 zty (OptionType.some ImplExpr zv) (BinderData.mk BinderInfo.default Multiplicity.many))) (impl_open zb zn2) zbt zn3) ",
                    "(zihty : ImplNotBVar zty) (zihv : ImplNotBVar zv) ",
                    "(zihb : ImplNotBVar (impl_open zb zn2)) => ImplUnit.mk) ",
                    // lit: 3 args, 0 IH
                    "(fun (in2 : Nat) (iG : LCtx) (ilt : ImplLit) => ImplUnit.mk) ",
                    // mdata: 6 args, 1 IH
                    "(fun (mn : Nat) (mn1 : Nat) (mG : LCtx) (me : ImplExpr) (mT : ImplExpr) ",
                    "(mh : ImplInfer tenv lps mn mG me mT mn1) (mih : ImplNotBVar me) => ImplUnit.mk) ",
                    "n G (ImplExpr.bvar i) T m h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "REFUTATION RULE (the 10th modelled arm): the deployed kernel never infers ",
                "a type for a raw bound variable — the release BVar arm is ",
                "`ExprKind::BVar(idx) => Err(TypeError::UnboundVariable(*idx))` ",
                "(tc/infer.rs:350), unconditional and before any other work — so ",
                "ImplInfer at a bvar is uninhabited. PROVED, not assumed: ImplInfer.rec over ",
                "the semireducible ImplNotBVar motive; every one of the nine constructors ",
                "concludes at a non-bvar head, so each minor's goal iota-reduces to ImplUnit ",
                "while the eliminated derivation's own index reduces the result to Empty. ",
                "Note this is a statement about layer 1 ONLY: layer 2 (KernelInfers.bvar, ",
                "TypingCtxConv.var) accepts a de Bruijn variable under its binder, and must ",
                "— the two describe different moments, which is exactly why the bridge is ",
                "representation-sensitive rather than identity-on-syntax. ZERO axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ImplInfer".to_string(),
                "ImplInfer.rec".to_string(),
                "ImplNotBVar".to_string(),
                "ImplUnit".to_string(),
                "Empty".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "impl_infer_tests.rs"]
mod tests;

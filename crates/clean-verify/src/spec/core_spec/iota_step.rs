// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment C (#2859 computational-iota/delta track): the computational
//! `iota_step` and its determinism — the KEYSTONE.
//!
//! C.1 (this file, first block): the list / application-spine substrate the
//! reduct function composes. All via explicit recursors (the proven
//! non-self-recursive `instantiate_bvar_geq`/`name_eqb` shape) or structural
//! self-calls passed as plain arguments (the proven `lift_at` app-arm shape) —
//! no nested match, no leading accumulators, no equation form (per the
//! adversarial design review). Recursion over the parametric `ListType` lowers
//! via `ListType.rec` (proven axiom-free: the elaborator's `appendR`/`listLen`
//! tests). See `designs/2026-06-14-computational-iota-delta-track.md` (Increment C).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_iota_step(&mut self) -> Result<(), SpecError> {
        // ===============================================================
        // C.1 — list / application-spine substrate over ListType KExpr.
        // ===============================================================

        // opt_bind: monadic bind for OptionType (chains the partial lookups in
        // iota_reduct). Generic over the element types.
        self.add_recursive_def(
            r"def opt_bind (α : Type) (β : Type) (o : OptionType α) (f : α → OptionType β) : OptionType β := OptionType.rec α (fun (_ : OptionType α) => OptionType β) (OptionType.none β) (fun (a : α) => f a) o",
            "OptionType monadic bind: none >>= f = none, some a >>= f = f a. Part of #2859 (Increment C).",
        )?;

        // list_append: append two KExpr lists (recursion via ListType.rec IH).
        self.add_recursive_def(
            r"def list_append (xs : ListType KExpr) (ys : ListType KExpr) : ListType KExpr := ListType.rec KExpr (fun (_ : ListType KExpr) => ListType KExpr) ys (fun (x : KExpr) (rest : ListType KExpr) (ih : ListType KExpr) => ListType.cons KExpr x ih) xs",
            "Append two KExpr lists. Part of #2859 (Increment C).",
        )?;

        // apply_spine: left-fold KExpr.app over an argument list, head trailing.
        // (args, head) recursing on args — head is the trailing varying param
        // (the proven extra-param shape, NOT a leading accumulator).
        self.add_recursive_def(
            r"def apply_spine (args : ListType KExpr) (head : KExpr) : KExpr := ListType.rec KExpr (fun (_ : ListType KExpr) => KExpr -> KExpr) (fun (h : KExpr) => h) (fun (x : KExpr) (rest : ListType KExpr) (ih : KExpr -> KExpr) => fun (h : KExpr) => ih (KExpr.app h x)) args head",
            "apply_spine [a0,..,an] head = app (.. (app head a0) ..) an (left-nested spine). Part of #2859 (Increment C).",
        )?;

        // kapp_args: the argument list of an application spine, head-to-tail.
        // Structural on the `app` field f; self-call passed to list_append.
        self.add_recursive_def(
            r"def kapp_args (e : KExpr) : ListType KExpr := match e with
| KExpr.sort n => ListType.nil KExpr
| KExpr.bvar i => ListType.nil KExpr
| KExpr.app f a => list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))
| KExpr.lam ty b => ListType.nil KExpr
| KExpr.pi ty b => ListType.nil KExpr
| KExpr.const n us => ListType.nil KExpr
| KExpr.let_ ty v b => ListType.nil KExpr
| KExpr.proj s i sub => ListType.nil KExpr
| KExpr.lit n => ListType.nil KExpr",
            "Argument list of an application spine: kapp_args (app (app h a0) a1) = [a0, a1]. Part of #2859 (Increment C).",
        )?;

        // list_tail: drop the first element (nil if empty).
        self.add_recursive_def(
            r"def list_tail (xs : ListType KExpr) : ListType KExpr := ListType.rec KExpr (fun (_ : ListType KExpr) => ListType KExpr) (ListType.nil KExpr) (fun (x : KExpr) (rest : ListType KExpr) (_ : ListType KExpr) => rest) xs",
            "Tail of a KExpr list (nil if empty). Part of #2859 (Increment C).",
        )?;

        // list_head: the first element, or none.
        self.add_recursive_def(
            r"def list_head (xs : ListType KExpr) : OptionType KExpr := ListType.rec KExpr (fun (_ : ListType KExpr) => OptionType KExpr) (OptionType.none KExpr) (fun (x : KExpr) (rest : ListType KExpr) (_ : OptionType KExpr) => OptionType.some KExpr x) xs",
            "Head of a KExpr list as an OptionType (none if empty). Part of #2859 (Increment C).",
        )?;

        // list_drop: drop the first n elements. Nat.rec with motive
        // `ListType KExpr -> ListType KExpr`, recursion via the IH.
        self.add_recursive_def(
            r"def list_drop (n : Nat) (xs : ListType KExpr) : ListType KExpr := Nat.rec (fun (_ : Nat) => ListType KExpr -> ListType KExpr) (fun (l : ListType KExpr) => l) (fun (m : Nat) (ih : ListType KExpr -> ListType KExpr) => fun (l : ListType KExpr) => ih (list_tail l)) n xs",
            "Drop the first n elements of a KExpr list. Part of #2859 (Increment C).",
        )?;

        // list_take: keep the first n elements.
        self.add_recursive_def(
            r"def list_take (n : Nat) (xs : ListType KExpr) : ListType KExpr := Nat.rec (fun (_ : Nat) => ListType KExpr -> ListType KExpr) (fun (l : ListType KExpr) => ListType.nil KExpr) (fun (m : Nat) (ih : ListType KExpr -> ListType KExpr) => fun (l : ListType KExpr) => ListType.rec KExpr (fun (_ : ListType KExpr) => ListType KExpr) (ListType.nil KExpr) (fun (x : KExpr) (rest : ListType KExpr) (_ : ListType KExpr) => ListType.cons KExpr x (ih rest)) l) n xs",
            "Keep the first n elements of a KExpr list. Part of #2859 (Increment C).",
        )?;

        // kexpr_const_name: the head const's Name, or none (for the recursor /
        // constructor name lookups). KExpr.rec discriminator.
        self.add_recursive_def(
            r"def kexpr_const_name (e : KExpr) : OptionType Name := KExpr.rec (fun (_ : KExpr) => OptionType Name) (fun (n : Level) => OptionType.none Name) (fun (i : Nat) => OptionType.none Name) (fun (f : KExpr) (a : KExpr) (_ : OptionType Name) (_ : OptionType Name) => OptionType.none Name) (fun (ty : KExpr) (b : KExpr) (_ : OptionType Name) (_ : OptionType Name) => OptionType.none Name) (fun (ty : KExpr) (b : KExpr) (_ : OptionType Name) (_ : OptionType Name) => OptionType.none Name) (fun (nm : Name) (us : ListType Level) => OptionType.some Name nm) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_ : OptionType Name) (_ : OptionType Name) (_ : OptionType Name) => OptionType.none Name) (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : OptionType Name) => OptionType.none Name) (fun (_ : Nat) => OptionType.none Name) e",
            "The head const's Name (none unless e is itself a const). Used after kapp_fn to read recursor/constructor names. Part of #2859 (Increment C).",
        )?;

        // list_length: length of a KExpr list.
        self.add_recursive_def(
            r"def list_length (xs : ListType KExpr) : Nat := ListType.rec KExpr (fun (_ : ListType KExpr) => Nat) Nat.zero (fun (x : KExpr) (rest : ListType KExpr) (ih : Nat) => Nat.succ ih) xs",
            "Length of a KExpr list. Part of #2859 (Increment C).",
        )?;

        // ===============================================================
        // C.2 — iota_reduct: the computational reduct (MajorAfterMinors path).
        // ===============================================================
        //
        // Mirrors the kernel try_iota_reduction (tc/reduction/mod.rs:66-345),
        // MajorAfterMinors only:
        //   args  = kapp_args e  = [params.., motives.., minors.., indices.., major, extras..]
        //   k     = num_params + num_motives + num_minors + num_indices  (major position)
        //   major = args[k];  cname = head const of major;  rule = recrule_for env recname cname
        //   prefix = first (num_params+num_motives+num_minors) args      (rhs binds these)
        //   fields = last `num_fields` args of the major (the ctor's own params dropped)
        //   extras = args after the major
        //   reduct = apply_spine extras (apply_spine fields (apply_spine prefix rhs))
        // Returns `none` for any non-redex (not const-headed / not a recursor /
        // major out of range / not constructor-headed / no rule), via opt_bind.
        //
        // Partiality + opaque `rhs` mean this is a TOTAL function (hence
        // deterministic by construction — the keystone). It is NOT yet
        // kernel-faithful: level-params instantiation, K, MajorAfterMotive,
        // literals, and the major-premise WHNF pre-pass are deferred (faithfulness
        // is a later env-wellformedness obligation, NOT a confluence axiom).
        self.add_recursive_def(
            r"def iota_reduct (env : RecEnv) (e : KExpr) : OptionType KExpr := opt_bind Name KExpr (kexpr_const_name (kapp_fn e)) (fun (recname : Name) => opt_bind RecMeta KExpr (recmeta_for env recname) (fun (meta : RecMeta) => opt_bind KExpr KExpr (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args e))) (fun (major : KExpr) => opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cname : Name) => opt_bind RecRule KExpr (recrule_for env recname cname) (fun (rule : RecRule) => OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args e)) (recrule_rhs rule))))))))))",
            "Computational iota reduct (MajorAfterMinors): the directed reduct of a recursor-applied-to-constructor redex, or none. Total function -> deterministic by construction. Part of #2859 (Increment C).",
        )?;

        // ===============================================================
        // C.3 — iota_step (the graph of iota_reduct) + determinism (KEYSTONE).
        // ===============================================================

        // iota_step env e e' : the directed step e -> e' holds iff the reduct
        // function maps e to `some e'`. The graph of a function, so it is a
        // FUNCTION — the determinism the abstract iota_reduces could never give.
        self.add_recursive_def(
            r"def iota_step (env : RecEnv) (e : KExpr) (e' : KExpr) : Prop := Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e')",
            "Directed iota step: iota_step env e e' holds iff iota_reduct env e = some e'. The graph of the reduct function. Part of #2859 (Increment C).",
        )?;

        // iota_step_deterministic: the reduct is unique. Since iota_step is the
        // graph of the FUNCTION iota_reduct, two reducts of the same redex are
        // both equal to `iota_reduct env e`, hence equal by some-injectivity. This
        // is the single new capability the abstract iota_reduces.mk (an undirected,
        // non-functional DefEq witness) structurally lacked — and the fact the
        // par_strips iota cross-joins need (Increment F).
        self.add_definition(SpecDefinition {
            name: "iota_step_deterministic".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e1) -> ",
                "Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e2) -> ",
                "Eq KExpr e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
                    "(h1 : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e1)) ",
                    "(h2 : Eq (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e2)) => ",
                    "option_some_inj KExpr e1 e2 ",
                    "(Eq.trans (OptionType KExpr) ",
                    "(OptionType.some KExpr e1) (iota_reduct env e) (OptionType.some KExpr e2) ",
                    "(Eq.symm (OptionType KExpr) (iota_reduct env e) (OptionType.some KExpr e1) h1) ",
                    "h2)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "iota_step determinism: iota_reduct env e = some e1 and = some e2 imply e1 = e2. ",
                "Free because iota_reduct is a total FUNCTION (graph + some-injectivity). The ",
                "directed-determinate capability the abstract iota_reduces lacked; consumed by the ",
                "par_strips iota cross-joins (Increment F). DerivedProved, zero axiom_deps. ",
                "Part of #2859 (Increment C, KEYSTONE)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduct".to_string(),
                "option_some_inj".to_string(),
                "Eq.symm".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ===============================================================
        // C.4 — spine / list computation-rule (unfolding) lemmas.
        // The kernel does not reduce through the spec-level ListType.rec wrapper,
        // so downstream equational proofs (substitution-commutation, the
        // par_strips iota arm) need these one-step unfolds. All Eq.refl
        // (DerivedProved, zero axiom_deps), mirroring Increment A's kapp_fn_app.
        // ===============================================================

        let unfold = |name: &str, type_src: &str, value_src: &str, desc: &str| SpecDefinition {
            name: name.to_string(),
            type_src: type_src.to_string(),
            value_src: Some(value_src.to_string()),
            is_axiom: false,
            description: desc.to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        };

        // apply_spine [] head = head
        self.add_definition(unfold(
            "apply_spine_nil",
            "forall (head : KExpr), Eq KExpr (apply_spine (ListType.nil KExpr) head) head",
            "fun (head : KExpr) => Eq.refl KExpr head",
            "Unfolding: apply_spine nil head = head. DerivedProved. Part of #2859 (Increment C).",
        ))?;

        // apply_spine (x :: rest) head = apply_spine rest (app head x)
        self.add_definition(unfold(
            "apply_spine_cons",
            "forall (x : KExpr) (rest : ListType KExpr) (head : KExpr), Eq KExpr (apply_spine (ListType.cons KExpr x rest) head) (apply_spine rest (KExpr.app head x))",
            "fun (x : KExpr) (rest : ListType KExpr) (head : KExpr) => Eq.refl KExpr (apply_spine rest (KExpr.app head x))",
            "Unfolding: apply_spine (x :: rest) head = apply_spine rest (app head x). DerivedProved. Part of #2859 (Increment C).",
        ))?;

        // list_append [] ys = ys
        self.add_definition(unfold(
            "list_append_nil",
            "forall (ys : ListType KExpr), Eq (ListType KExpr) (list_append (ListType.nil KExpr) ys) ys",
            "fun (ys : ListType KExpr) => Eq.refl (ListType KExpr) ys",
            "Unfolding: list_append nil ys = ys. DerivedProved. Part of #2859 (Increment C).",
        ))?;

        // list_append (x :: rest) ys = x :: (list_append rest ys)
        self.add_definition(unfold(
            "list_append_cons",
            "forall (x : KExpr) (rest : ListType KExpr) (ys : ListType KExpr), Eq (ListType KExpr) (list_append (ListType.cons KExpr x rest) ys) (ListType.cons KExpr x (list_append rest ys))",
            "fun (x : KExpr) (rest : ListType KExpr) (ys : ListType KExpr) => Eq.refl (ListType KExpr) (ListType.cons KExpr x (list_append rest ys))",
            "Unfolding: list_append (x :: rest) ys = x :: list_append rest ys. DerivedProved. Part of #2859 (Increment C).",
        ))?;

        // kapp_args (app f a) = list_append (kapp_args f) [a]
        self.add_definition(unfold(
            "kapp_args_app",
            "forall (f : KExpr) (a : KExpr), Eq (ListType KExpr) (kapp_args (KExpr.app f a)) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)))",
            "fun (f : KExpr) (a : KExpr) => Eq.refl (ListType KExpr) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr)))",
            "Unfolding: kapp_args (app f a) = list_append (kapp_args f) [a]. DerivedProved. Part of #2859 (Increment C).",
        ))?;

        // list_tail (x :: rest) = rest
        self.add_definition(unfold(
            "list_tail_cons",
            "forall (x : KExpr) (rest : ListType KExpr), Eq (ListType KExpr) (list_tail (ListType.cons KExpr x rest)) rest",
            "fun (x : KExpr) (rest : ListType KExpr) => Eq.refl (ListType KExpr) rest",
            "Unfolding: list_tail (x :: rest) = rest. DerivedProved. Part of #2859 (Increment C).",
        ))?;

        // list_head (x :: rest) = some x
        self.add_definition(unfold(
            "list_head_cons",
            "forall (x : KExpr) (rest : ListType KExpr), Eq (OptionType KExpr) (list_head (ListType.cons KExpr x rest)) (OptionType.some KExpr x)",
            "fun (x : KExpr) (rest : ListType KExpr) => Eq.refl (OptionType KExpr) (OptionType.some KExpr x)",
            "Unfolding: list_head (x :: rest) = some x. DerivedProved. Part of #2859 (Increment C).",
        ))?;

        // list_drop 0 xs = xs
        self.add_definition(unfold(
            "list_drop_zero",
            "forall (xs : ListType KExpr), Eq (ListType KExpr) (list_drop Nat.zero xs) xs",
            "fun (xs : ListType KExpr) => Eq.refl (ListType KExpr) xs",
            "Unfolding: list_drop 0 xs = xs. DerivedProved. Part of #2859 (Increment C).",
        ))?;

        // list_drop (succ n) xs = list_drop n (list_tail xs)
        self.add_definition(unfold(
            "list_drop_succ",
            "forall (n : Nat) (xs : ListType KExpr), Eq (ListType KExpr) (list_drop (Nat.succ n) xs) (list_drop n (list_tail xs))",
            "fun (n : Nat) (xs : ListType KExpr) => Eq.refl (ListType KExpr) (list_drop n (list_tail xs))",
            "Unfolding: list_drop (succ n) xs = list_drop n (list_tail xs). DerivedProved. Part of #2859 (Increment C).",
        ))?;

        // list_length (x :: rest) = succ (list_length rest)
        self.add_definition(unfold(
            "list_length_cons",
            "forall (x : KExpr) (rest : ListType KExpr), Eq Nat (list_length (ListType.cons KExpr x rest)) (Nat.succ (list_length rest))",
            "fun (x : KExpr) (rest : ListType KExpr) => Eq.refl Nat (Nat.succ (list_length rest))",
            "Unfolding: list_length (x :: rest) = succ (list_length rest). DerivedProved. Part of #2859 (Increment C).",
        ))?;

        // ===============================================================
        // C.6 — spine structural lemmas: apply_spine_snoc + the spine round-trip.
        // The faithfulness facts of the spine decomposition, by ListType.rec /
        // KExpr.rec induction chained through the C.4/C.5 unfolding lemmas (the
        // kernel does not auto-reduce through the spec recursors). DerivedProved,
        // zero axiom_deps. These anchor the instantiate_at-commutation chain (E).
        // ===============================================================

        // apply_spine (list_append xs [a]) head = app (apply_spine xs head) a.
        self.add_definition(SpecDefinition {
            name: "apply_spine_snoc".to_string(),
            type_src: concat!(
                "forall (xs : ListType KExpr) (a : KExpr) (head : KExpr), ",
                "Eq KExpr (apply_spine (list_append xs (ListType.cons KExpr a (ListType.nil KExpr))) head) ",
                "(KExpr.app (apply_spine xs head) a)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (xs : ListType KExpr) (a : KExpr) (head : KExpr) => ",
                    "ListType.rec KExpr ",
                    "(fun (xs0 : ListType KExpr) => forall (a0 : KExpr) (head0 : KExpr), ",
                    "Eq KExpr (apply_spine (list_append xs0 (ListType.cons KExpr a0 (ListType.nil KExpr))) head0) ",
                    "(KExpr.app (apply_spine xs0 head0) a0)) ",
                    // nil case
                    "(fun (a0 : KExpr) (head0 : KExpr) => ",
                    "Eq.trans KExpr ",
                    "(apply_spine (list_append (ListType.nil KExpr) (ListType.cons KExpr a0 (ListType.nil KExpr))) head0) ",
                    "(apply_spine (ListType.cons KExpr a0 (ListType.nil KExpr)) head0) ",
                    "(KExpr.app (apply_spine (ListType.nil KExpr) head0) a0) ",
                    "(Eq.cong (ListType KExpr) KExpr (fun (L : ListType KExpr) => apply_spine L head0) ",
                    "(list_append (ListType.nil KExpr) (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                    "(ListType.cons KExpr a0 (ListType.nil KExpr)) ",
                    "(list_append_nil (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                    "(Eq.trans KExpr ",
                    "(apply_spine (ListType.cons KExpr a0 (ListType.nil KExpr)) head0) ",
                    "(KExpr.app head0 a0) ",
                    "(KExpr.app (apply_spine (ListType.nil KExpr) head0) a0) ",
                    "(Eq.trans KExpr ",
                    "(apply_spine (ListType.cons KExpr a0 (ListType.nil KExpr)) head0) ",
                    "(apply_spine (ListType.nil KExpr) (KExpr.app head0 a0)) ",
                    "(KExpr.app head0 a0) ",
                    "(apply_spine_cons a0 (ListType.nil KExpr) head0) ",
                    "(apply_spine_nil (KExpr.app head0 a0))) ",
                    "(Eq.symm KExpr (KExpr.app (apply_spine (ListType.nil KExpr) head0) a0) (KExpr.app head0 a0) ",
                    "(Eq.cong KExpr KExpr (fun (h : KExpr) => KExpr.app h a0) ",
                    "(apply_spine (ListType.nil KExpr) head0) head0 (apply_spine_nil head0))))) ",
                    // cons case
                    "(fun (x : KExpr) (rest : ListType KExpr) ",
                    "(ih : forall (a0 : KExpr) (head0 : KExpr), ",
                    "Eq KExpr (apply_spine (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr))) head0) ",
                    "(KExpr.app (apply_spine rest head0) a0)) => ",
                    "fun (a0 : KExpr) (head0 : KExpr) => ",
                    "Eq.trans KExpr ",
                    "(apply_spine (list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a0 (ListType.nil KExpr))) head0) ",
                    "(apply_spine (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr))) (KExpr.app head0 x)) ",
                    "(KExpr.app (apply_spine (ListType.cons KExpr x rest) head0) a0) ",
                    "(Eq.trans KExpr ",
                    "(apply_spine (list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a0 (ListType.nil KExpr))) head0) ",
                    "(apply_spine (ListType.cons KExpr x (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr)))) head0) ",
                    "(apply_spine (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr))) (KExpr.app head0 x)) ",
                    "(Eq.cong (ListType KExpr) KExpr (fun (L : ListType KExpr) => apply_spine L head0) ",
                    "(list_append (ListType.cons KExpr x rest) (ListType.cons KExpr a0 (ListType.nil KExpr))) ",
                    "(ListType.cons KExpr x (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                    "(list_append_cons x rest (ListType.cons KExpr a0 (ListType.nil KExpr)))) ",
                    "(apply_spine_cons x (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr))) head0)) ",
                    "(Eq.trans KExpr ",
                    "(apply_spine (list_append rest (ListType.cons KExpr a0 (ListType.nil KExpr))) (KExpr.app head0 x)) ",
                    "(KExpr.app (apply_spine rest (KExpr.app head0 x)) a0) ",
                    "(KExpr.app (apply_spine (ListType.cons KExpr x rest) head0) a0) ",
                    "(ih a0 (KExpr.app head0 x)) ",
                    "(Eq.symm KExpr (KExpr.app (apply_spine (ListType.cons KExpr x rest) head0) a0) ",
                    "(KExpr.app (apply_spine rest (KExpr.app head0 x)) a0) ",
                    "(Eq.cong KExpr KExpr (fun (h : KExpr) => KExpr.app h a0) ",
                    "(apply_spine (ListType.cons KExpr x rest) head0) (apply_spine rest (KExpr.app head0 x)) ",
                    "(apply_spine_cons x rest head0))))) ",
                    "xs a head"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "apply_spine (list_append xs [a]) head = app (apply_spine xs head) a. By ListType.rec ",
                "on xs chained through the C.4/C.5 unfolding lemmas. The snoc law of the spine fold; ",
                "anchors the spine round-trip. DerivedProved, zero axiom_deps. Part of #2859 (Increment C)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "apply_spine".to_string(),
                "list_append".to_string(),
                "ListType.rec".to_string(),
                "apply_spine_nil".to_string(),
                "apply_spine_cons".to_string(),
                "list_append_nil".to_string(),
                "list_append_cons".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kapp_spine_roundtrip: apply_spine (kapp_args e) (kapp_fn e) = e — the
        // spine decomposition is faithful (head + args reassemble the term). By
        // KExpr.rec on e: base ctors have empty args (apply_spine_nil); the app
        // case uses apply_spine_snoc + the head IH. The reassembly law the
        // instantiate_at-commutation chain (Increment E) builds on.
        self.add_definition(SpecDefinition {
            name: "kapp_spine_roundtrip".to_string(),
            type_src:
                "forall (e : KExpr), Eq KExpr (apply_spine (kapp_args e) (kapp_fn e)) e".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) => KExpr.rec ",
                    "(fun (e0 : KExpr) => Eq KExpr (apply_spine (kapp_args e0) (kapp_fn e0)) e0) ",
                    "(fun (n : Level) => apply_spine_nil (KExpr.sort n)) ",
                    "(fun (i : Nat) => apply_spine_nil (KExpr.bvar i)) ",
                    "(fun (f : KExpr) (a : KExpr) ",
                    "(ih_f : Eq KExpr (apply_spine (kapp_args f) (kapp_fn f)) f) ",
                    "(ih_a : Eq KExpr (apply_spine (kapp_args a) (kapp_fn a)) a) => ",
                    "Eq.trans KExpr ",
                    "(apply_spine (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) (kapp_fn f)) ",
                    "(KExpr.app (apply_spine (kapp_args f) (kapp_fn f)) a) ",
                    "(KExpr.app f a) ",
                    "(apply_spine_snoc (kapp_args f) a (kapp_fn f)) ",
                    "(Eq.cong KExpr KExpr (fun (h : KExpr) => KExpr.app h a) ",
                    "(apply_spine (kapp_args f) (kapp_fn f)) f ih_f)) ",
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(ih_ty : Eq KExpr (apply_spine (kapp_args ty) (kapp_fn ty)) ty) ",
                    "(ih_b : Eq KExpr (apply_spine (kapp_args b) (kapp_fn b)) b) => ",
                    "apply_spine_nil (KExpr.lam ty b)) ",
                    "(fun (ty : KExpr) (b : KExpr) ",
                    "(ih_ty : Eq KExpr (apply_spine (kapp_args ty) (kapp_fn ty)) ty) ",
                    "(ih_b : Eq KExpr (apply_spine (kapp_args b) (kapp_fn b)) b) => ",
                    "apply_spine_nil (KExpr.pi ty b)) ",
                    "(fun (nm : Name) (us : ListType Level) => apply_spine_nil (KExpr.const nm us)) ",
                    "(fun (ty : KExpr) (v : KExpr) (b : KExpr) ",
                    "(ih_ty : Eq KExpr (apply_spine (kapp_args ty) (kapp_fn ty)) ty) ",
                    "(ih_v : Eq KExpr (apply_spine (kapp_args v) (kapp_fn v)) v) ",
                    "(ih_b : Eq KExpr (apply_spine (kapp_args b) (kapp_fn b)) b) => ",
                    "apply_spine_nil (KExpr.let_ ty v b)) ",
                    "(fun (s : Name) (i : Nat) (sub : KExpr) ",
                    "(ih_sub : Eq KExpr (apply_spine (kapp_args sub) (kapp_fn sub)) sub) => ",
                    "apply_spine_nil (KExpr.proj s i sub)) ",
                    "(fun (n : Nat) => apply_spine_nil (KExpr.lit n)) ",
                    "e"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "apply_spine (kapp_args e) (kapp_fn e) = e: the spine decomposition is faithful ",
                "(head + argument list reassemble the term). By KExpr.rec on e — base constructors ",
                "via apply_spine_nil, the app case via apply_spine_snoc + the head IH. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment C)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "apply_spine".to_string(),
                "kapp_args".to_string(),
                "kapp_fn".to_string(),
                "KExpr.rec".to_string(),
                "apply_spine_nil".to_string(),
                "apply_spine_snoc".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

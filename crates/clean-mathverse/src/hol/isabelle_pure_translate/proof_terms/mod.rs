// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-term translation: the `AbsP`/`Abst`/`PBound` de-Bruijn machinery,
//! `equal_elim`/`combination` handling, the spine collector and β-reducer, and the
//! two large `impl Ctx` proof-walking blocks.
//!
//! Part of the [`super`] Pure proof-term → clean kernel translator; split
//! out of the original single-file module purely for readability — the code is
//! moved verbatim, the behaviour is byte-identical.

use std::collections::BTreeMap;

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr};

use super::super::isabelle_pure::{IsaProof, IsaProvenTheorem, IsaTerm, IsaType};
use super::*;

/// Kind of de Bruijn binder. clean has a single bvar space, but Pure keeps
/// **two separate** counters (see Isabelle `Pure/proofterm.ML`,
/// `incr_bv_same`: `AbsP` bumps the proof level `Plev`, `Abst` bumps the term
/// level `tlev`; and `prf_loose_Pbvar1` increments its counter on `AbsP` but
/// **not** on `Abst`):
/// - `Proof` (`AbsP`, `Pure.imp` hypothesis): counted by `PBound` ONLY.
/// - `ProofTerm` (`Abst`, ⋀-intro): counted by term `Bound` ONLY — it binds a
///   *term* variable, so although syntactically a "proof abstraction" it does
///   **not** occupy a `PBound` slot (a `PBound` references a proof, never an
///   `Abst`'s term variable).
/// - `Term` (term-level `Abs`, `Pure.all` bound var): counted by term `Bound`,
///   NOT by `PBound`.
///
/// The clean index returned by [`indexed_bvar`] is always the *absolute* stack
/// depth (clean has one bvar space); the `BKind` predicate only selects WHICH
/// binder the i-th `PBound` / term `Bound` resolves to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BKind {
    Proof,
    ProofTerm,
    Term,
    /// An **elided implicit sort-hypothesis** `AbsP` — a fully-typed (`zproof`)
    /// binder discharging an `OFCLASS`/sort-constraint hypothesis the statement
    /// does not spell (Isabelle attaches it to the type variable's sort) whose
    /// membership embeds to the vacuous `True`. No clean lambda is emitted for
    /// it, so it occupies a `PBound` **slot** (Isabelle's proof-binder counter
    /// still counts the `AbsP`) but NO clean bvar depth; a `PBound` that
    /// resolves to it becomes the vacuous witness `True.intro` (see
    /// [`proof_bvar_or_witness`]).
    ElidedSortHyp,
}

/// One entry in the shared de Bruijn binder context.
#[derive(Clone, Debug)]
pub(crate) struct Binder {
    pub(crate) kind: BKind,
    /// Embedded clean type (HOL type for a term binder, proposition for a proof
    /// binder).
    pub(crate) ty: Expr,
}

/// clean bvar index + type of the `j`-th binder a Pure **term** `Bound` sees
/// (`ProofTerm`/`Term` only — skips pure proof hypotheses).
pub(crate) fn term_bvar(binders: &[Binder], j: usize) -> Option<(u32, Expr)> {
    indexed_bvar(binders, j, |k| matches!(k, BKind::ProofTerm | BKind::Term))
}

/// What a Pure `PBound i` resolves to (see [`proof_bvar_slot`]).
pub(crate) enum PboundSlot {
    /// An ordinary `Proof` binder: the clean bvar at this depth.
    Bvar(u32),
    /// An **elided implicit sort-hypothesis** slot ([`BKind::ElidedSortHyp`]):
    /// Isabelle's `PBound` counter counts the discharged `AbsP`, but no clean
    /// lambda was emitted for it. The reference must become a witness for the
    /// slot's embedded membership proposition (carried here): `True.intro` for
    /// the vacuous `True`, or a quantified hypothesis param for a registered
    /// structured class ([`Ctx::sort_hyp_witness`]).
    Elided(Expr),
}

/// Resolve the slot a Pure `PBound i` references: the matching `Proof` binder
/// (`AbsP` — skips both term-level lambdas and `Abst` term-variable binders,
/// matching Isabelle's `PBound` counter which is bumped by `AbsP` but not
/// `Abst`; see `Pure/proofterm.ML`) or an elided implicit sort-hypothesis slot,
/// which occupies a `PBound` index but no clean bvar depth.
pub(crate) fn proof_bvar_slot(binders: &[Binder], i: usize) -> Option<PboundSlot> {
    let mut seen = 0;
    let mut depth: u32 = 0;
    for b in binders.iter().rev() {
        if matches!(b.kind, BKind::Proof | BKind::ElidedSortHyp) {
            if seen == i {
                return Some(match b.kind {
                    BKind::ElidedSortHyp => PboundSlot::Elided(b.ty.clone()),
                    _ => PboundSlot::Bvar(depth),
                });
            }
            seen += 1;
        }
        if !matches!(b.kind, BKind::ElidedSortHyp) {
            depth += 1;
        }
    }
    None
}

/// The embedded proposition (binder type) of the proof binder a Pure `PBound i`
/// resolves to. Used by [`Ctx::infer_proof_prop`] to recover the hypothesis type
/// of a redex `AbsP { h: None }` applied to a `PBound` argument. An elided
/// implicit sort-hypothesis slot reports its (vacuous) `True` proposition.
pub(crate) fn proof_bvar_ty(binders: &[Binder], i: usize) -> Option<Expr> {
    indexed_bvar(binders, i, |k| {
        matches!(k, BKind::Proof | BKind::ElidedSortHyp)
    })
    .map(|(_, ty)| ty)
}

pub(crate) fn indexed_bvar(
    binders: &[Binder],
    n: usize,
    counts: impl Fn(BKind) -> bool,
) -> Option<(u32, Expr)> {
    let mut seen = 0;
    // clean bvar depth counts only the binders that emit a clean lambda — an
    // elided sort-hypothesis slot occupies a `PBound` index but no clean depth.
    let mut depth: u32 = 0;
    for b in binders.iter().rev() {
        if counts(b.kind) {
            if seen == n {
                return Some((depth, b.ty.clone()));
            }
            seen += 1;
        }
        if !matches!(b.kind, BKind::ElidedSortHyp) {
            depth += 1;
        }
    }
    None
}

/// Extract the operand object-type `α` of a HOL `=`/`≡` from the equality
/// constant's own type `α ⇒ α ⇒ _`, falling back to `None`.
pub(crate) fn eq_operand_type(eq_const_ty: &IsaType) -> Option<&IsaType> {
    match eq_const_ty {
        IsaType::Type { n, a } if n == "fun" && a.len() == 2 => Some(&a[0]),
        _ => None,
    }
}

/// Split a HOL function type `'a ⇒ 'b` into its domain and codomain, or `None`
/// if it is not a `fun` arrow. Used by the int-quotient bridge embedders
/// ([`Ctx::embed_pair`], [`Ctx::embed_case_prod`], [`Ctx::embed_map_fun`]) to
/// read the element/operation types off the instantiated constant type.
pub(crate) fn fun_split(ty: &IsaType) -> Option<(&IsaType, &IsaType)> {
    match ty {
        IsaType::Type { n, a } if n == "fun" && a.len() == 2 => Some((&a[0], &a[1])),
        _ => None,
    }
}

/// If `tm` is a (Trueprop-stripped) equality `eq lhs rhs` (`Pure.eq`/`HOL.eq`/
/// `=`), return `(eq_const_type, lhs)`. The constant's own type carries the
/// operand type `α ⇒ α ⇒ _`. Used by the `Eq.refl` fallback for definitional
/// `lhs ≡ rhs` theorems whose proof body is absent from the export.
pub(crate) fn eq_statement_lhs(tm: &IsaTerm) -> Option<(&IsaType, &IsaTerm)> {
    match tm {
        // See through the `Trueprop` / `Pure.prop` identity coercions.
        IsaTerm::App { f, a }
            if is_const(f, "HOL.Trueprop")
                || is_const(f, "Trueprop")
                || is_const(f, "Pure.prop") =>
        {
            eq_statement_lhs(a)
        }
        // `(eq $ lhs) $ rhs`.
        IsaTerm::App { f, a: _rhs } => {
            if let IsaTerm::App { f: eqf, a: lhs } = f.as_ref() {
                if let IsaTerm::Const { n, t } = eqf.as_ref() {
                    if n == "Pure.eq" || n == "HOL.eq" || n == "=" {
                        return Some((t, lhs));
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Whether `tm` is a sort/type-class constraint head (`HOL.type_class`, any
/// `…_class`, or `Pure.sort_constraint`) — these are vacuous in the embedding.
pub(crate) fn is_class_app(tm: &IsaTerm) -> bool {
    matches!(tm, IsaTerm::Const { n, .. }
        if n.ends_with("_class") || n == "Pure.sort_constraint")
}

/// Whether `tm` is a **sort-constraint hypothesis** term — a class-membership
/// application `c_class (TYPE('a))` / `Pure.sort_constraint (TYPE('a))` (the
/// proof-term spelling of `OFCLASS('a, c)`). The zproof export records these as
/// explicit `AbsP` hypotheses even when the statement does NOT spell them
/// (Isabelle attaches the constraint to the type variable's sort); such an
/// *implicit* discharge is transparent in this embedding when the membership is
/// vacuous — see the elision arm in [`Ctx::translate_proof`].
pub(crate) fn is_sort_hyp_term(tm: &IsaTerm) -> bool {
    match tm {
        IsaTerm::App { f, a } => is_class_app(f) && class_type_arg(a).is_some(),
        _ => false,
    }
}

/// Whether `thm` is a candidate for the trailing [`ClassMembership::NonemptyErase`]
/// modes: it carries at least one leading `OFCLASS`/sort-constraint premise AND
/// either
///   - concludes a `Pure.conjunction` bundle (`simp_thms` / `all_simps` and kin) —
///     the shape [`super::def_axioms::prove_conjunction_bundle`] discharges, or
///   - concludes a **single** quantifier simp equation (`HOL.eq` whose LHS is a
///     `HOL.All`/`HOL.Ex` — a vacuous, one-point, or `∨`/`⟶` miniscoping law) — the
///     shape [`super::def_axioms::prove_nonempty_single_leaf`] discharges.
///
/// Gating here keeps the extra trailing modes off every non-candidate theorem, so
/// they pay no extra translation. Purely syntactic on the recorded statement; the
/// mode is trailing + additive, so a false-positive here can only cost a declined
/// translation attempt, never a mis-flip.
pub(crate) fn nonempty_erase_applicable(thm: &IsaProvenTheorem) -> bool {
    let mut cur = &thm.prop;
    let mut saw_sort_prem = false;
    loop {
        // Strip a `Trueprop` / `Pure.prop` wrapper.
        if let IsaTerm::App { f, a } = cur {
            if is_const(f, "HOL.Trueprop") || is_const(f, "Trueprop") || is_const(f, "Pure.prop") {
                cur = a;
                continue;
            }
        }
        match cur {
            // `Pure.all (λx. body)` — a leading `⋀x.` binder.
            IsaTerm::App { f, a } if is_const(f, "Pure.all") => match a.as_ref() {
                IsaTerm::Abs { b, .. } => cur = b,
                _ => return false,
            },
            // `Pure.imp A B` = `App(App(Const Pure.imp, A), B)`, the bundle
            // conclusion head `Pure.conjunction A B`, or a single `HOL.eq lhs rhs`
            // quantifier-simp conclusion.
            IsaTerm::App { f, a: rhs } => {
                let IsaTerm::App { f: head, a: prem } = f.as_ref() else {
                    return false;
                };
                if is_const(head, "Pure.imp") {
                    if is_sort_hyp_term(prem) {
                        saw_sort_prem = true;
                    }
                    cur = rhs;
                } else if is_const(head, "Pure.conjunction") {
                    return saw_sort_prem;
                } else if is_const(head, "HOL.eq") {
                    // Standalone quantifier simp law: `(∀x. …) = …` / `(∃x. …) = …`.
                    // `prem` is the equation's LHS.
                    return saw_sort_prem && is_quantifier_headed(prem);
                } else {
                    return false;
                }
            }
            _ => return false,
        }
    }
}

/// Whether `tm` is headed by a HOL quantifier (`HOL.All`/`HOL.Ex`) applied to its
/// predicate — the LHS shape of every vacuous / one-point / miniscoping simp law.
fn is_quantifier_headed(tm: &IsaTerm) -> bool {
    matches!(tm, IsaTerm::App { f, .. } if is_const(f, "HOL.All") || is_const(f, "HOL.Ex"))
}

/// Whether a leftover proof SPINE argument (an argument past the referenced
/// entry's verified telescope) is a **sort-constraint witness with no binder to
/// fill**: an explicit `OfClass` node, or a `PBound` that resolves to an elided
/// implicit sort-hypothesis slot ([`PboundSlot::Elided`]). The referenced
/// entry's telescope never materialized the constraint (it was erased / elided
/// in the mode that verified the entry), so applying the witness to the
/// already-saturated head is always ill-typed (`NotAFunction`) — the callers
/// drop it instead; the kernel re-checks the result.
pub(crate) fn is_leftover_sort_witness(arg: &SpineArg, binders: &[Binder]) -> bool {
    match arg {
        SpineArg::Proof(IsaProof::OfClass { .. }) => true,
        // A `PBound` witness: an elided implicit slot, or a real binder whose
        // recorded proposition is the vacuous `True` (the consumer's own
        // spelled-but-erased sort premise) — either way a sort witness the
        // saturated head has no binder for.
        SpineArg::Proof(IsaProof::Bound { i }) => {
            matches!(
                proof_bvar_slot(binders, *i as usize),
                Some(PboundSlot::Elided(_))
            ) || proof_bvar_ty(binders, *i as usize).is_some_and(|ty| ty == Expr::const_str("True"))
        }
        _ => false,
    }
}

/// Whether an expected Pi DOMAIN spells a (possibly erased) **sort-constraint
/// premise**: the vacuous `True`, or a class-membership proposition headed by a
/// registered class def-const (`isabelle.def.<…>_class α ops`). Used by the
/// expecting-side implicit sort-hypothesis elision to distinguish an
/// expectation that DOES spell the discharged constraint (keep the lambda)
/// from one that does not (elide the binder).
pub(crate) fn expected_dom_spells_sort_premise(dom: &Expr) -> bool {
    use clean_kernel::expr::ExprKind;
    let mut head = dom;
    while let ExprKind::App(f, _) = head.kind() {
        head = f;
    }
    match head.kind() {
        ExprKind::Const(n, _) => {
            let s = n.to_string();
            s == "True" || (s.starts_with("isabelle.def.") && s.ends_with("_class"))
        }
        _ => false,
    }
}

/// Whether a recorded proof contains any `Thm`/`Axm` reference carrying a
/// non-empty explicit `tyinst`/`tminst` instantiation table — a **fully-typed
/// (`zproof`) export marker** (the legacy export never records these tables).
/// Computed once per theorem to gate the zproof-only recoveries
/// ([`Ctx::zproof_mode`]) so legacy translation stays byte-identical.
pub(crate) fn proof_has_inst_tables(p: &IsaProof) -> bool {
    match p {
        IsaProof::Thm { tyinst, tminst, .. } | IsaProof::Axm { tyinst, tminst, .. } => {
            !tyinst.is_empty() || !tminst.is_empty()
        }
        IsaProof::AppP { f, a } => proof_has_inst_tables(f) || proof_has_inst_tables(a),
        IsaProof::AppT { f, .. } => proof_has_inst_tables(f),
        IsaProof::AbsP { b, .. } | IsaProof::Abst { b, .. } => proof_has_inst_tables(b),
        _ => false,
    }
}

/// Whether a recorded proof is a **candidate for the namespace-crossed root
/// lane** ([`Ctx::try_root_sort_absp_expecting`]): a fully-typed (`zproof`)
/// export whose root is a chain of at least one sort-hypothesis `AbsP` over a
/// `Thm`-headed spine with GENERIC (identity) instantiation tables. A
/// conservative SUPERSET of the lane's own runtime precondition (the
/// spelled-premise test needs the embedded statement, which is not available
/// here) — used by the driver's `escalation_modes` to append the dedicated
/// `RootLane::On` trailing modes only where the lane could possibly fire, so
/// the extra per-line translation cost is paid only by candidate nodes.
pub(crate) fn root_lane_applicable(p: &IsaProof) -> bool {
    if !proof_has_inst_tables(p) {
        return false;
    }
    let mut peeled = 0usize;
    let mut cur = p;
    while let IsaProof::AbsP { h: Some(hyp), b } = cur {
        if !is_sort_hyp_term(hyp) {
            return false;
        }
        peeled += 1;
        cur = b;
    }
    if peeled == 0 {
        return false;
    }
    let (head, _spine) = collect_spine(cur);
    match head {
        IsaProof::Thm { tyinst, tminst, .. } => insts_generic(tyinst, tminst),
        _ => false,
    }
}

/// Whether a recorded proof is a **candidate for the proof-β-redex expectation
/// lane** (bidir stage 2): a fully-typed (`zproof`) export whose root is a chain
/// of at least one **leading premise** `AbsP`/`Abst` binder over a body headed
/// (via [`collect_spine`]) by an `AbsP` — i.e. a `let`-style proof β-redex,
/// `(λh:H. b) arg`. These are the non-equational discharge-chain roots (the
/// swap/iff-style twins: prove an intermediate `H` once and apply it several
/// times) whose leading `Pure.imp`/`⋀` premises put them OUT of
/// `root_expecting`'s empty-queue scope and OUT of [`eq_tower_applicable`]'s
/// equational-axiom-head scope, yet whose interior `Thm` legs desync exactly the
/// same way (the `expected=Sort got=FVar` phantom-operand reject the census
/// decoded). Routed through [`Ctx::translate_proof_expecting`] on the statement,
/// which peels the leading premises against the expected `Pi` and reduces each
/// proof redex threading the expectation into the body
/// ([`Ctx::translate_proof_expecting`]'s β-redex arm) so it reaches the interior
/// `Thm` legs.
///
/// Deliberately scoped to a **redex (`AbsP`) head**, NOT a bare `Thm`-spine head:
/// plain Thm-spine roots under premises are the far more numerous shape and are
/// already covered by [`root_lane_applicable`] / the forward `apply_thm` path, so
/// admitting them here would append four extra eager per-line translations
/// (`translate_all_modes`) across a large fraction of the corpus for little
/// additional reach. The redex-head family is comparatively rare and is the
/// genuinely-new coverage.
///
/// Conservative marker used by `escalation_modes` to append the dedicated
/// `RootLane::BidirEqTower` trailing modes only where the lane could fire; the
/// lane runs LAST (after every historical mode kernel-rejected) and every term
/// it builds is kernel-re-checked, so a non-candidate mis-marked here at most
/// wastes one translation — never miscounts. Requires ≥1 peeled leading binder
/// so the empty-premise generic-Thm root stays with `root_expecting`
/// (byte-identical) rather than being re-run redundantly here.
pub(crate) fn thm_spine_root_applicable(p: &IsaProof) -> bool {
    if !proof_has_inst_tables(p) {
        return false;
    }
    let mut cur = p;
    let mut peeled = 0usize;
    while let IsaProof::AbsP { b, .. } | IsaProof::Abst { b, .. } = cur {
        cur = b;
        peeled += 1;
    }
    if peeled == 0 {
        return false;
    }
    let (head, _spine) = collect_spine(cur);
    matches!(head, IsaProof::AbsP { .. })
}

/// Whether a recorded proof is a **candidate for the recursive
/// expectation-propagation lane** ([`Ctx::bidir_tower`], `RootLane::BidirEqTower`):
/// a fully-typed (`zproof`) export whose root — after peeling the leading
/// structural `AbsP`/`Abst` binder chain — is a **pure equational-tower node**:
/// a spine headed by one of the Pure/HOL equality-congruence axioms
/// (`equal_elim`/`transitive`/`symmetric`/`combination`/`reflexive`) or by a
/// `Thm` reference whose instantiation tables leave the operands GENERIC
/// ([`insts_generic`] — the schematic-reference shape whose real operands are
/// pinned only by the surrounding inference). These are exactly the frontier
/// nodes the reject census decoded as operand-desync (`?x.0` vs `x` filled from
/// the recorded table instead of the expected type). A conservative marker used
/// by the driver's `escalation_modes` to append the dedicated
/// `RootLane::BidirEqTower` trailing modes ONLY where the lane could fire, so the
/// extra per-line translation cost is paid only by candidate nodes; the lane is
/// kernel-re-checked and runs last, so a non-candidate mis-marked here would at
/// most waste one translation (never miscount).
pub(crate) fn eq_tower_applicable(p: &IsaProof) -> bool {
    if !proof_has_inst_tables(p) {
        return false;
    }
    // Peel the leading structural binder chain (⋀-intro / ⟹-discharge): the
    // expectation-propagation walk re-derives each binder's domain from the
    // expected `Pi` and threads the codomain down.
    let mut cur = p;
    while let IsaProof::AbsP { b, .. } | IsaProof::Abst { b, .. } = cur {
        cur = b;
    }
    let (head, _spine) = collect_spine(cur);
    // Only the pure equational-tower AXIOM heads — a bare `Thm`-spine root is
    // *general Thm-spine expectation*, deliberately OUT of stage-1 scope (the
    // `root_lane`/`apply_thm_expecting` machinery already covers what it can), so
    // the lane never fires on it (keeping those nodes' historical translation
    // byte-identical).
    match head {
        IsaProof::Axm { name, .. } => matches!(
            name.as_str(),
            "Pure.equal_elim"
                | "Pure.transitive"
                | "HOL.trans"
                | "Pure.symmetric"
                | "HOL.sym"
                | "Pure.combination"
                | "Pure.reflexive"
                | "HOL.refl"
        ),
        _ => false,
    }
}

/// The object type `'a` carried by a class-membership argument — the
/// `Pure.type` constant whose own type is `itself('a)`. Returns that `'a`.
pub(crate) fn class_type_arg(itself_arg: &IsaTerm) -> Option<&IsaType> {
    let t = match itself_arg {
        IsaTerm::Const { t, .. } | IsaTerm::Free { t, .. } | IsaTerm::Var { t, .. } => t,
        _ => return None,
    };
    match t {
        IsaType::Type { n, a } if n == "itself" && a.len() == 1 => Some(&a[0]),
        _ => None,
    }
}

/// Whether a fully-typed (`zproof`) reference's `tyinst`/`tminst` tables are the
/// **identity instantiation** — every schematic type variable mapped to itself
/// (`?'a.0 ↦ ?'a.0`) and every schematic term variable mapped to itself
/// (`?x.0 ↦ ?x.0`, or its unvarified `Free x`). Isabelle emits such *generic*
/// tables when a reference is used schematically (the actual instantiation is
/// determined by the surrounding inference, not recorded on the node): a bare
/// top-level identity `Thm` is a restatement of its dependency, and a mid-proof
/// identity reference must be solved **bidirectionally** from its expected
/// proposition rather than by filling the generic table entries verbatim (which
/// manufactures fresh, unconstrained parameters). Empty tables count as identity.
pub(crate) fn insts_all_identity(
    tyinst: &[super::super::isabelle_pure::IsaTypeInst],
    tminst: &[super::super::isabelle_pure::IsaTermInst],
) -> bool {
    tyinst.iter().all(identity_tyinst) && tminst.iter().all(identity_tminst)
}

/// Whether one `tyinst` entry maps its schematic type variable to itself.
///
/// Two identity spellings: `TVar` to itself, and the **unvarified `TFree`** of
/// the same base name under a key index `-1` or `0`. The `-1` key is the zproof
/// encoding of the referenced statement's own FREE type variable (Isabelle
/// `Pure/zterm.ML` encodes `TFree a` as `ZTVar (a, ~1)`), so an entry
/// `?'a.-1 ↦ TFree 'a` maps that free to itself — the generic (identity) shape.
pub(crate) fn identity_tyinst(ti: &super::super::isabelle_pure::IsaTypeInst) -> bool {
    use super::super::isabelle_pure::IsaType;
    match &ti.ty {
        IsaType::TVar { n, i } => *n == ti.n && *i == ti.i,
        IsaType::TFree { n } => *n == ti.n && (ti.i == 0 || ti.i == -1),
        _ => false,
    }
}

/// Whether one `tminst` entry maps its schematic term variable to itself (or its
/// unvarified `Free` of the same base name).
///
/// The `Free` case has two key flavors: index `0` (a varified statement's `?x.0`
/// left generic, `?x.0 ↦ x` — the round-1 shape) and index `-1` — the zproof
/// encoding of the referenced statement's own FREE variable (Isabelle
/// `Pure/zterm.ML` encodes `Free x` as `ZVar (x, ~1)`), so an entry
/// `?x.-1 ↦ Free x` maps that free to itself. The `-1` flavor is what the
/// `Pure.combination`/`reflexive`/`symmetric` primitive references carry when
/// Isabelle leaves them schematic (`?f ↦ f`, `?x ↦ x` under genuinely-recorded
/// types): treating it as identity routes those chains through the
/// bidirectional operand recovery instead of manufacturing phantom `f`/`x`
/// parameters the kernel then rejects (the `expected=FVar got=FVar` /
/// `Free a` vs `?a.0` operand-keying mismatch).
pub(crate) fn identity_tminst(tm: &super::super::isabelle_pure::IsaTermInst) -> bool {
    match &tm.t {
        IsaTerm::Var { n, i, .. } => *n == tm.n && *i == tm.i,
        IsaTerm::Free { n, .. } => *n == tm.n && (tm.i == 0 || tm.i == -1),
        _ => false,
    }
}

/// Whether a fully-typed reference's tables leave its **term operands generic** —
/// the zproof export's schematic-use shape whose actual operands are pinned only
/// by the surrounding inference. Two cases:
/// - a non-empty `tminst` that is entirely the identity (`?x ↦ x`): the TYPES may
///   be genuinely instantiated (`'a ↦ prop`) while the term witnesses are not
///   recorded (the dominant `Pure.combination`/`reflexive` chain shape);
/// - an empty `tminst` with a non-empty all-identity `tyinst` (a bare schematic
///   reference).
/// Legacy references (both tables empty) and genuinely term-instantiated
/// references return `false`.
pub(crate) fn insts_generic(
    tyinst: &[super::super::isabelle_pure::IsaTypeInst],
    tminst: &[super::super::isabelle_pure::IsaTermInst],
) -> bool {
    if !tminst.is_empty() {
        tminst.iter().all(identity_tminst)
    } else {
        !tyinst.is_empty() && tyinst.iter().all(identity_tyinst)
    }
}

/// Whether a proof's spine head is an `Axm`/`Thm` reference whose instantiation
/// tables leave the **term operands generic** ([`insts_generic`]) — the
/// fully-typed (`zproof`) export's schematic-reference shape whose actual
/// operands must be recovered bidirectionally from the surrounding context.
/// Legacy references (empty tables — operands on the term spine) and
/// genuinely-instantiated references return `false`, so callers gate the
/// bidirectional-first recovery to exactly the generic zproof shape and leave
/// every previously-handled path untouched.
pub(crate) fn spine_head_generic_inst(p: &IsaProof) -> bool {
    let (head, _) = collect_spine(p);
    match head {
        IsaProof::Axm { tyinst, tminst, .. } | IsaProof::Thm { tyinst, tminst, .. } => {
            insts_generic(tyinst, tminst)
        }
        _ => false,
    }
}

/// Build the embedded object-level equation `@Eq α x y` (the shape
/// [`Ctx::infer_proof_prop`] and the bidirectional recovery channels exchange).
pub(crate) fn mk_eq_expr(alpha: Expr, x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [alpha, x, y],
    )
}

/// Whether a `Pure.combination` reference's recorded function type (`tyinst`
/// `'a`) is the `bool ⇒ prop` **coercion** — the type of `Trueprop`. Such a
/// combination congruence-steps *through the wrapper the embedding erases*
/// (`Trueprop X ≡ Trueprop Y` from `X ≡ Y`), so a bidirectional recovery whose
/// expected operands are already `Trueprop`-stripped must delegate to the
/// node's ARGUMENT leg instead of decomposing the stripped operands against
/// this (one-level-higher) node.
pub(crate) fn combination_at_prop_coercion(
    tyinst: &[super::super::isabelle_pure::IsaTypeInst],
) -> bool {
    let fun_ty = tyinst
        .iter()
        .find(|ti| ti.n == "'a")
        .or_else(|| tyinst.first())
        .map(|ti| &ti.ty);
    let Some(IsaType::Type { n, a }) = fun_ty else {
        return false;
    };
    n == "fun"
        && a.len() == 2
        && matches!(&a[0], IsaType::Type { n, .. } if n == "bool" || n == "HOL.bool")
        && matches!(&a[1], IsaType::Type { n, .. } if n == "prop")
}

/// Whether an Isabelle term mentions any `Free` variable. The zproof export
/// records a derivation box's INTERNAL (unvarified) variable names as `Free`s
/// (`Free a`/`Free b`) while the exported statement carries their varified
/// schematic counterparts (`?a.0`/`?b.0`); the two embed under DIFFERENT
/// parameter keys (`a` vs `a.0`), so an instantiation-table operand that
/// mentions a `Free` can never match the statement's quantified parameters —
/// callers use this to prefer recovering such operands from the surrounding
/// premises' propositions (which are statement-keyed by construction).
pub(crate) fn term_contains_free(t: &IsaTerm) -> bool {
    match t {
        IsaTerm::Free { .. } => true,
        IsaTerm::App { f, a } => term_contains_free(f) || term_contains_free(a),
        IsaTerm::Abs { b, .. } => term_contains_free(b),
        IsaTerm::Const { .. } | IsaTerm::Var { .. } | IsaTerm::Bound { .. } => false,
    }
}

/// One entry on a proof application spine.
pub(crate) enum SpineArg {
    Term(IsaTerm),
    Proof(IsaProof),
}

/// Collect the application spine of a proof: head plus args in left-to-right
/// order (`(((h a1) a2) a3)`).
pub(crate) fn collect_spine(p: &IsaProof) -> (&IsaProof, Vec<SpineArg>) {
    let mut args = Vec::new();
    let mut cur = p;
    loop {
        match cur {
            IsaProof::AppP { f, a } => {
                // Sort witnesses (`PClass`) are kept and translate to `True.intro`
                // (matching the `True` sort-constraint premises), preserving arity.
                args.push(SpineArg::Proof((**a).clone()));
                cur = f;
            }
            IsaProof::AppT { f, a } => {
                if let Some(t) = a {
                    args.push(SpineArg::Term(t.clone()));
                } else {
                    args.push(SpineArg::Term(IsaTerm::Bound { i: -1 }));
                }
                cur = f;
            }
            _ => break,
        }
    }
    args.reverse();
    (cur, args)
}

// ---------------------------------------------------------------------------
// Isabelle-level β-reduction of proof redexes.
//
// The raw export omits the bound-variable types of `Abst { ty: None }` /
// `AbsP { h: None }`. When such a binder is *immediately applied* (a proof-level
// redex `(λ-chain. body) arg…`), we can avoid recovering the omitted types
// entirely by performing the β-reduction at the IsaProof level — substituting
// each spine argument into the body — and translating the **reduced** body,
// which no longer contains the typeless binders. This is the same reduction the
// kernel would perform after type-checking; doing it first sidesteps the missing
// type annotations. The kernel re-checks the final term, so this is a pure
// (soundness-neutral) normalization.
//
// The two de Bruijn index spaces (per the `BKind` doc): a Pure term `Bound`
// counts `Abs`/`Abst`/`Pure.all` term binders; a `PBound` counts `AbsP`/`Abst`
// proof binders. An `Abst` occupies a slot in BOTH spaces; an `AbsP` only in the
// proof space. Eliminating a binder substitutes its index-0 occurrences and
// decrements the deeper indices in the affected space(s).
// ---------------------------------------------------------------------------

/// Shift free term `Bound` indices `≥ cutoff` by `delta` within a term.
pub(crate) fn shift_term(t: &IsaTerm, cutoff: i64, delta: i64) -> IsaTerm {
    // Budget guard (see [`shift_proof`]): cut a pathological term clone. Return
    // the O(1) `Bound 0` sentinel; the poisoned result is discarded upstream.
    if !super::subst_step_ok() {
        return IsaTerm::Bound { i: 0 };
    }
    match t {
        IsaTerm::Bound { i } if *i >= cutoff => IsaTerm::Bound { i: i + delta },
        IsaTerm::Bound { .. }
        | IsaTerm::Const { .. }
        | IsaTerm::Free { .. }
        | IsaTerm::Var { .. } => t.clone(),
        IsaTerm::Abs { n, t: ty, b } => IsaTerm::Abs {
            n: n.clone(),
            t: ty.clone(),
            b: Box::new(shift_term(b, cutoff + 1, delta)),
        },
        IsaTerm::App { f, a } => IsaTerm::App {
            f: Box::new(shift_term(f, cutoff, delta)),
            a: Box::new(shift_term(a, cutoff, delta)),
        },
    }
}

/// Substitute term `Bound t_cut` with `repl` inside `t` (capture-avoiding), and
/// decrement deeper term indices — the term-space half of one β-step.
pub(crate) fn subst_term_in_term(t: &IsaTerm, t_cut: i64, repl: &IsaTerm) -> IsaTerm {
    // Budget guard (see [`shift_proof`]): cut a pathological term substitution
    // (a big `repl` duplicated at many `Bound` positions). O(1) `Bound 0`
    // sentinel; the poisoned result is discarded by `translate_redex`.
    if !super::subst_step_ok() {
        return IsaTerm::Bound { i: 0 };
    }
    match t {
        IsaTerm::Bound { i } if *i == t_cut => shift_term(repl, 0, t_cut),
        IsaTerm::Bound { i } if *i > t_cut => IsaTerm::Bound { i: i - 1 },
        IsaTerm::Bound { .. }
        | IsaTerm::Const { .. }
        | IsaTerm::Free { .. }
        | IsaTerm::Var { .. } => t.clone(),
        IsaTerm::Abs { n, t: ty, b } => IsaTerm::Abs {
            n: n.clone(),
            t: ty.clone(),
            b: Box::new(subst_term_in_term(b, t_cut + 1, repl)),
        },
        IsaTerm::App { f, a } => IsaTerm::App {
            f: Box::new(subst_term_in_term(f, t_cut, repl)),
            a: Box::new(subst_term_in_term(a, t_cut, repl)),
        },
    }
}

/// Walk a proof, applying `on_term` to every embedded term with the current
/// term-binder depth, and recursing through proof binders (tracking which depth
/// each space is at via the closure's captured counters is awkward, so the term
/// depth is threaded explicitly). Used to substitute a term argument (for an
/// eliminated `Abst`) into a proof body.
pub(crate) fn map_proof_terms(
    p: &IsaProof,
    t_depth: i64,
    f: &dyn Fn(&IsaTerm, i64) -> IsaTerm,
) -> IsaProof {
    // Budget guard (see [`shift_proof`]): cut a pathological term-into-proof
    // substitution (the Zorn/`Abst`-elimination blowup — a big term duplicated
    // across the proof). O(1) `Nop`; the poisoned result is discarded by
    // `translate_redex`, which rejects the line.
    if !super::subst_step_ok() {
        return IsaProof::Nop;
    }
    match p {
        IsaProof::Thm { .. }
        | IsaProof::Axm { .. }
        | IsaProof::Bound { .. }
        | IsaProof::Min
        | IsaProof::Oracle { .. }
        | IsaProof::Nop
        | IsaProof::Other => p.clone(),
        IsaProof::Hyp { p: tm } => IsaProof::Hyp { p: f(tm, t_depth) },
        IsaProof::OfClass { ty, c } => IsaProof::OfClass {
            ty: ty.clone(),
            c: c.clone(),
        },
        // `Abst` adds a term binder (and a proof binder); the term depth rises.
        IsaProof::Abst { ty, b } => IsaProof::Abst {
            ty: ty.clone(),
            b: Box::new(map_proof_terms(b, t_depth + 1, f)),
        },
        // `AbsP` adds a proof binder only — term depth unchanged.
        IsaProof::AbsP { h, b } => IsaProof::AbsP {
            h: h.as_ref().map(|hyp| f(hyp, t_depth)),
            b: Box::new(map_proof_terms(b, t_depth, f)),
        },
        IsaProof::AppP { f: pf, a } => IsaProof::AppP {
            f: Box::new(map_proof_terms(pf, t_depth, f)),
            a: Box::new(map_proof_terms(a, t_depth, f)),
        },
        IsaProof::AppT { f: pf, a } => IsaProof::AppT {
            f: Box::new(map_proof_terms(pf, t_depth, f)),
            a: a.as_ref().map(|tm| f(tm, t_depth)),
        },
    }
}

/// β-substitute an eliminated `Abst`'s **term** argument into the body proof:
/// replace term `Bound 0` (in the body's term space) with `repl`, decrementing
/// deeper term indices. An `Abst` occupies no `PBound` slot, so the proof space
/// is left untouched (Isabelle `subst_bounds`).
pub(crate) fn subst_tbound0_in_proof(body: &IsaProof, repl: &IsaTerm) -> IsaProof {
    map_proof_terms(body, 0, &|tm, depth| subst_term_in_term(tm, depth, repl))
}

/// Shift `PBound` indices `≥ cutoff` by `delta` within a proof (for lifting a
/// substituted proof under inner proof binders). Only `AbsP` raises the cutoff —
/// `Abst` binds a *term* variable and occupies no `PBound` slot (Isabelle
/// `incr_bv_same`: `AbsP` → `Plev + 1`, `Abst` → `tlev + 1`).
pub(crate) fn shift_proof(p: &IsaProof, cutoff: i64, delta: i64) -> IsaProof {
    // Budget guard: a quadratic/exponential clone over a pathological proof term
    // is cut here. On poison return the O(1) `Nop` sentinel — NOT `p.clone()`,
    // which for an internal node deep-clones the whole (huge) subtree and would
    // itself grind. The result is discarded by `translate_redex` (it rejects the
    // line on poison), so the sentinel value is irrelevant. No-op (recurses
    // normally) when no budget is configured.
    if !super::subst_step_ok() {
        return IsaProof::Nop;
    }
    match p {
        IsaProof::Bound { i } if *i >= cutoff => IsaProof::Bound { i: i + delta },
        IsaProof::Bound { .. }
        | IsaProof::Thm { .. }
        | IsaProof::Axm { .. }
        | IsaProof::Hyp { .. }
        | IsaProof::OfClass { .. }
        | IsaProof::Min
        | IsaProof::Oracle { .. }
        | IsaProof::Nop
        | IsaProof::Other => p.clone(),
        // `Abst` does NOT occupy a `PBound` slot → cutoff unchanged.
        IsaProof::Abst { ty, b } => IsaProof::Abst {
            ty: ty.clone(),
            b: Box::new(shift_proof(b, cutoff, delta)),
        },
        IsaProof::AbsP { h, b } => IsaProof::AbsP {
            h: h.clone(),
            b: Box::new(shift_proof(b, cutoff + 1, delta)),
        },
        IsaProof::AppP { f, a } => IsaProof::AppP {
            f: Box::new(shift_proof(f, cutoff, delta)),
            a: Box::new(shift_proof(a, cutoff, delta)),
        },
        IsaProof::AppT { f, a } => IsaProof::AppT {
            f: Box::new(shift_proof(f, cutoff, delta)),
            a: a.clone(),
        },
    }
}

/// β-substitute an eliminated `AbsP`'s **proof** argument into the body proof:
/// replace `PBound 0` with `repl` (lifted under inner proof binders) and
/// decrement deeper `PBound` indices. The term space is unaffected (an `AbsP`
/// does not occupy a term-binder slot).
pub(crate) fn subst_pbound0_in_proof(body: &IsaProof, repl: &IsaProof, p_cut: i64) -> IsaProof {
    // Budget guard (see [`shift_proof`]): cut a pathological quadratic/exponential
    // clone. Return the O(1) `Nop` sentinel (a deep `body.clone()` would itself
    // grind); the poisoned result is discarded by `translate_redex`.
    if !super::subst_step_ok() {
        return IsaProof::Nop;
    }
    match body {
        IsaProof::Bound { i } if *i == p_cut => shift_proof(repl, 0, p_cut),
        IsaProof::Bound { i } if *i > p_cut => IsaProof::Bound { i: i - 1 },
        IsaProof::Bound { .. }
        | IsaProof::Thm { .. }
        | IsaProof::Axm { .. }
        | IsaProof::Hyp { .. }
        | IsaProof::OfClass { .. }
        | IsaProof::Min
        | IsaProof::Oracle { .. }
        | IsaProof::Nop
        | IsaProof::Other => body.clone(),
        // `Abst` does NOT occupy a `PBound` slot → cutoff unchanged.
        IsaProof::Abst { ty, b } => IsaProof::Abst {
            ty: ty.clone(),
            b: Box::new(subst_pbound0_in_proof(b, repl, p_cut)),
        },
        IsaProof::AbsP { h, b } => IsaProof::AbsP {
            h: h.clone(),
            b: Box::new(subst_pbound0_in_proof(b, repl, p_cut + 1)),
        },
        IsaProof::AppP { f, a } => IsaProof::AppP {
            f: Box::new(subst_pbound0_in_proof(f, repl, p_cut)),
            a: Box::new(subst_pbound0_in_proof(a, repl, p_cut)),
        },
        IsaProof::AppT { f, a } => IsaProof::AppT {
            f: Box::new(subst_pbound0_in_proof(f, repl, p_cut)),
            a: a.clone(),
        },
    }
}

/// One β-step on a redex whose head binder is `head` (`Abst` or `AbsP`) and whose
/// first argument is `arg`: returns the reduced body, or `None` if the
/// binder/argument kinds do not match (a malformed redex). Eliminating an `Abst`
/// substitutes the term arg into the **term** space only (an `Abst` occupies no
/// `PBound` slot, so the proof space is unchanged — Isabelle `subst_bounds`);
/// eliminating an `AbsP` substitutes the proof arg (proof space).
pub(crate) fn beta_step(head: &IsaProof, arg: &SpineArg) -> Option<IsaProof> {
    match (head, arg) {
        (IsaProof::Abst { b, .. }, SpineArg::Term(t)) => Some(subst_tbound0_in_proof(b, t)),
        (IsaProof::AbsP { b, .. }, SpineArg::Proof(q)) => Some(subst_pbound0_in_proof(b, q, 0)),
        _ => None,
    }
}

mod apply;
mod apply_expecting;
mod args;
mod bootstrap;
mod premises;
mod translate;

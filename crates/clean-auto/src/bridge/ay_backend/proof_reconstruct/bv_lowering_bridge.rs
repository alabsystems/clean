// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Encoding-fidelity bridge: `Unsat <clauses>` ⟹ `bvEq (lhs) (rhs)`.
//!
//! # The verified-codegen payload
//!
//! [`super::bv_blast_reflection::certify_unsat_by_reflection`] produces a FULLY
//! zero-trust kernel proof of `Clean.Res.Unsat <clauses>` — the clause set of the
//! bit-blasted obligation `not(bvAdd a b == bvAdd b a)` is unsatisfiable. That on
//! its own does NOT yet say anything about `Clean.BV4` arithmetic: it is a fact
//! about a `List (List Nat)`. This module supplies the missing half — the proof
//! that the clause set FAITHFULLY ENCODES the lowering identity, so that `Unsat`
//! of the clauses *implies* the bit-vector identity.
//!
//! ## What the bridge proves (and how it validates the bit-blast)
//!
//! `Clean.Res.Unsat cs ≡ (H : Nat → Prop) → resConsistent H → resExclusive H →
//! allSat H cs → False`. To turn that into `bvEq lhs rhs` we EXHIBIT the model the
//! bit-blast intends: the **Boolean assignment read off the computational BV4
//! operands**. Concretely, for symbolic `a b : Clean.BV4`:
//!
//!   * `f_ab : Nat → Bool` maps each Tseitin *variable* id to its gate `Bool` term
//!     over `a`/`b`'s bits — `InputA{k} ↦ bit k a`, `InputB{k} ↦ bit k b`, and
//!     every gate output to the BV4 gate expression (`xor3`/`maj`/`xnor`/…) of its
//!     inputs (`super::theory_lemma_bv_compute_blast::build_reflection`). This is
//!     EXACTLY the trust-cg lowering's representation of the ripple-carry adder.
//!   * `H_ab := Clean.Res.boolModel f_ab` is the induced literal model; the kernel
//!     theorems `boolModelConsistent`/`boolModelExclusive` discharge
//!     `resConsistent`/`resExclusive` FOR FREE.
//!   * `allSat H_ab cs` is proved clause by clause. **Each gate clause** is a real
//!     Tseitin clause of its BV4 gate — proved by `Bool.rec` case analysis over the
//!     clause's free **leaf-bit cone** (the `a`/`b` input bits it transitively
//!     depends on), from the `#18` computational defs (`bvAdd`/`xor3`/`maj`). The gate
//!     OUTPUT vars are not free: each reduces through its `xor3`/`maj`/`xnor` def from
//!     the leaves, so an individual Tseitin clause — which is a tautology only
//!     relative to the gate constraint `out ↔ gate(ins)`, NOT over its vars as free
//!     Bools — is genuinely discharged. The leaf cone reaches 8 bits for the high-bit
//!     XnorEq clauses; to keep the fidelity `check_type` tractable each gate clause is
//!     registered as its OWN `Definition <prefix>_gate_<id>` and kernel-checked in
//!     isolation, then referenced by name in the `allSat` And-chain — so the kernel
//!     never reduces all 130 ripple-carry gate trees inside one monolithic term
//!     (which peaked >100 GB / OOM). **The disequality clause** `(¬e_0 ∨ … ∨ ¬e_{n-1})`
//!     is proved from the assumed `Not (bvEq lhs rhs)`: a `false` bit-equality var
//!     `e_i` satisfies its `¬e_i` literal, and on the all-equal branch the per-bit
//!     equalities (obtained through `xnorTrueImpEq` over the bit-blast's `LhsOut_i`
//!     / `RhsOut_i` OUTPUT terms — def-eq to `bit i (bvAdd a b)` / `bit i (bvAdd b a)`)
//!     assemble `bvEq lhs rhs`, contradicting the assumption.
//!
//! The per-bit equality goes THROUGH `xnorTrueImpEq (LhsOut_i) (RhsOut_i)`, whose
//! arguments are the bit-blasted ripple-carry OUTPUT bits — so the kernel reduces
//! the `bvAdd` gate trees to validate the encoding. The bridge NEVER cites
//! `bvAdd_comm`; the identity is recovered solely from the bit-blast's clause
//! structure being unsatisfiable. That is the verified-codegen point: it certifies
//! that the *clauses* faithfully lower the identity, not merely that the identity
//! holds.
//!
//! Finally `Classical.byContradiction` (FOUNDATIONAL) turns the assembled
//! `Not (bvEq lhs rhs) → False` into `bvEq lhs rhs`.

use ay_proof::bv_blast_export::{BitLemmaKind, BvBlastProof, ClauseProvenance, Lit};
use clean_kernel::bitvec_compute::names as cnames;
use clean_kernel::bitvec_compute::BvNames;
use clean_kernel::bool_model::names as mnames;
use clean_kernel::name::Name;
use clean_kernel::resolution_check::encode_lit_lit;
use clean_kernel::resolution_soundness::names as rsnames;
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, Level, TypeChecker};

use super::theory_lemma_bv_compute_blast::{
    build_reflection, lit_bool, BvComputeBlastError, Reflection,
};

/// Outcome of a successful lowering-fidelity bridge: a kernel term of type
/// `bvEq lhs rhs` (or, in failure form, a `Not (bvEq lhs rhs) → False`).
pub struct LoweringBridge {
    /// Kernel proof term of `bvEq lhs rhs`, fully closed (no open fvars).
    pub bv_eq_term: Expr,
    /// The `bvEq lhs rhs` proposition the term inhabits.
    pub bv_eq_goal: Expr,
    /// Number of gate clauses kernel-justified from the BV4 defs.
    pub gate_clauses_proved: usize,
}

// ── small Expr helpers ──────────────────────────────────────────────────────────

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
fn false_c() -> Expr {
    Expr::const_str("False")
}
fn u1() -> Level {
    Level::succ(Level::zero())
}
fn eq_bool(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![u1()]),
        [bool_ty(), x, y],
    )
}
/// `Holds(b) := (b = Bool.true)` (the `boolModel` literal prop after reduction).
fn holds(b: Expr) -> Expr {
    eq_bool(b, btrue())
}
fn or_t(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Or"), vec![]), [a, b])
}
fn or_inl(a: Expr, b: Expr, ha: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Or.inl"), vec![]),
        [a, b, ha],
    )
}
fn or_inr(a: Expr, b: Expr, hb: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Or.inr"), vec![]),
        [a, b, hb],
    )
}
fn and_t(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [a, b])
}
fn list_nat() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        nat_ty(),
    )
}
fn list_cons_nat(h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
        [nat_ty(), h, t],
    )
}
fn list_nil_nat() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        nat_ty(),
    )
}
fn list_list_nat() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        list_nat(),
    )
}
fn list_cons_ll(h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
        [list_nat(), h, t],
    )
}
fn list_nil_ll() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        list_nat(),
    )
}
/// `Clean.Res.boolModel f` — the `Nat → Prop` model.
fn bool_model(f: &Expr) -> Expr {
    Expr::app(Expr::const_str(mnames::BOOL_MODEL), f.clone())
}
/// `Clean.Res.boolModelLit f l`.
fn bool_model_lit(f: &Expr, l: Expr) -> Expr {
    Expr::apps(Expr::const_str(mnames::BOOL_MODEL_LIT), [f.clone(), l])
}
/// `Clean.Res.clauseOr H c`.
fn clause_or(h: &Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.Res.clauseOr"), [h.clone(), c])
}
/// `Clean.Res.allSat H db`.
fn all_sat(h: &Expr, db: Expr) -> Expr {
    Expr::apps(Expr::const_str(rsnames::ALL_SAT), [h.clone(), db])
}

// ── the var-table Boolean assignment `f_ab : Nat → Bool` ────────────────────────

/// Build `f_ab : Nat → Bool` — a finite `Nat.rec` lookup ladder mapping variable id
/// `v` to its reflected gate `Bool` term (`refl.term[v]`), defaulting to
/// `Bool.false` beyond the table. So `f_ab v ≡ refl.term[v]` for every real var,
/// and (composed with `boolModelLit`) `boolModelLit f_ab (encode_lit v neg)` reduces
/// to `refl.term[v]` (positive) / `Bool.not refl.term[v]` (negative).
///
/// Shape: `fun (v : Nat) => Nat.rec t_0 (fun p_0 _ => Nat.rec t_1 (fun p_1 _ => …
/// Bool.false) p_0) v`, i.e. a nested `Nat.rec` ladder where the successor case
/// peels one index and recurses on the predecessor. Built with `fvar` scrutinees
/// (then abstracted) to avoid de Bruijn bookkeeping.
fn build_var_table_fn(refl: &Reflection, fresh: &Fresh) -> Expr {
    let (v_id, v) = fresh.fvar();
    let body = lookup_ladder(&refl.term, &v, fresh);
    Expr::lam(BinderInfo::Default, nat_ty(), body.abstract_fvar(v_id))
}

/// `Nat.rec terms[0] (fun p _ => <ladder over terms[1..] scrutinising p>) scrut`,
/// bottoming out in `Bool.false`. `scrut` is the (fvar) index to dispatch on.
fn lookup_ladder(terms: &[Expr], scrut: &Expr, fresh: &Fresh) -> Expr {
    let Some((head, tail)) = terms.split_first() else {
        return bfalse();
    };
    let motive = Expr::lam(BinderInfo::Default, nat_ty(), bool_ty());
    // succ-case: fun (p : Nat) (ih : Bool) => <ladder over tail scrutinising p>
    let (p_id, p) = fresh.fvar();
    let (ih_id, _ih) = fresh.fvar();
    let inner = lookup_ladder(tail, &p, fresh);
    let succ_case = {
        let lam_ih = Expr::lam(BinderInfo::Default, bool_ty(), inner.abstract_fvar(ih_id));
        Expr::lam(BinderInfo::Default, nat_ty(), lam_ih.abstract_fvar(p_id))
    };
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![u1()]);
    Expr::apps(nat_rec, [motive, head.clone(), succ_case, scrut.clone()])
}

/// Source of fresh `FVarId`s (mirrors the sibling reconstructor's `Fresh`).
pub(crate) struct Fresh {
    next: std::cell::Cell<u64>,
}
impl Fresh {
    pub(crate) fn new() -> Self {
        Self {
            next: std::cell::Cell::new(2_000_000),
        }
    }
    pub(crate) fn fvar(&self) -> (FVarId, Expr) {
        let id = self.next.get();
        self.next.set(id + 1);
        let fid = FVarId::new(id);
        (fid, Expr::fvar(fid))
    }
}

// ── clauseOr-shaped proofs (right-folded into False) ────────────────────────────

/// The `Or`-chain `clauseOr H c ≡ Or (H l0) (Or (H l1) (… (Or (H l_{k-1}) False)))`.
/// We mirror its shape on the REFLECTED props `holds(lit_bool l_i)` (def-eq to
/// `boolModel f l_i`). `clause_or_props` returns that prop list (no trailing False;
/// the fold tail is `False`).
fn clause_or_type_props(props: &[Expr]) -> Expr {
    // right fold: Or p0 (Or p1 (... (Or p_{k-1} False)))
    let mut acc = false_c();
    for p in props.iter().rev() {
        acc = or_t(p.clone(), acc);
    }
    acc
}

/// Inject a proof of `props[pos]` into the `clauseOr`-shaped `Or`-chain
/// `Or p0 (Or p1 (… False))` as `Or.inr^pos (Or.inl proof)`.
fn inject_clause_or(props: &[Expr], pos: usize, proof: Expr) -> Expr {
    // suffix tail type at depth d = Or p_d (Or p_{d+1} ... False)
    fn tail_from(props: &[Expr], d: usize) -> Expr {
        let mut acc = false_c();
        for p in props[d..].iter().rev() {
            acc = or_t(p.clone(), acc);
        }
        acc
    }
    // At position pos: head = props[pos], tail = tail_from(pos+1). inl proof.
    let head = props[pos].clone();
    let tail = tail_from(props, pos + 1);
    let mut acc = or_inl(head, tail, proof);
    // wrap with Or.inr for each preceding literal pos-1 .. 0
    for d in (0..pos).rev() {
        let head_d = props[d].clone();
        let tail_d = tail_from(props, d + 1);
        acc = or_inr(head_d, tail_d, acc);
    }
    acc
}

/// Prove `clauseOr H c` for a GATE (Tseitin) clause `c`, by `Bool.rec` case analysis
/// on the gate's **direct input signals** (`gate_inputs`, the lemma's `ins` reflected
/// `Bool` terms — at most 3: `x`/`y`/`carry`). The gate OUTPUT var is NOT split: it is
/// reduced through its `xor3`/`maj`/`xnor`/`not` def once the inputs are ground in a
/// branch, so the gate semantics are validated by definitional reduction.
///
/// This is the crux of the soundness/tractability balance:
///   * SOUND — an individual Tseitin clause is a tautology only relative to the gate
///     constraint `out ↔ gate(ins)`, so the output must be *computed* (never free).
///     Splitting on the inputs and letting `out`'s reflected `gate(ins)` reduce does
///     exactly that. (Splitting on `out` as a free `Bool` would be unsound — e.g.
///     `(¬LhsOut0 ∨ a0 ∨ b0 ∨ carry)` is falsifiable at `out=true, a0=b0=carry=false`.)
///   * TRACTABLE — at most 2³ = 8 ground branches per clause, regardless of how many
///     `a`/`b` leaf bits the gate's inputs transitively depend on. The earlier
///     leaf-CONE split reached 2⁸ branches for the high-bit gates, re-expanding the
///     whole ripple-carry gate tree under every `Bool.rec` motive (>100 GB / OOM).
///
/// `Bool.rec` on the (possibly symbolic) input term type-checks regardless of whether
/// the scrutinee is canonical: the proof inhabits `motive scrut` by β, and the two
/// branches inhabit `motive Bool.false`/`motive Bool.true`. At each leaf the chosen
/// literal's `lit_bool` reduces to `Bool.true`, discharged by `Eq.refl`. PROVED from
/// the BV4 gate defs — nothing assumed.
fn prove_gate_clause_or(
    refl: &Reflection,
    clause_id: u32,
    lits: &[Lit],
    gate_inputs: &[u32],
) -> Result<Expr, BvComputeBlastError> {
    // Split only on NON-CONSTANT inputs. A `ConstFalse`/`ConstTrue` input reflects to
    // `Bool.false`/`Bool.true`, which the kernel reduces directly — splitting it (and
    // substituting `refl.term[v]` = a bare `Bool` constant) would be both pointless and
    // a too-broad subterm replacement. Distinct vars only, preserving input order.
    let mut inputs: Vec<u32> = Vec::new();
    for &v in gate_inputs {
        if is_bool_const(&refl.term[v as usize]) || inputs.contains(&v) {
            continue;
        }
        inputs.push(v);
    }
    gate_split(refl, clause_id, lits, &inputs, &mut Vec::new())
}

/// `true` iff `e` is the bare `Bool.true`/`Bool.false` constant.
fn is_bool_const(e: &Expr) -> bool {
    use clean_kernel::ExprKind;
    matches!(e.kind(), ExprKind::Const(n, _) if {
        let s = n.to_string();
        s == "Bool.true" || s == "Bool.false"
    })
}

/// Recursive `Bool.rec` over the gate's `inputs` (var ids). `assigned` records the
/// `(input-var, bool)` choices; at a full assignment every clause literal's reflected
/// term is ground (inputs substituted, the output `gate(ins)` reduced), so we pick the
/// first satisfied literal and inject its `Eq.refl Bool.true`.
fn gate_split(
    refl: &Reflection,
    clause_id: u32,
    lits: &[Lit],
    inputs: &[u32],
    assigned: &mut Vec<(u32, bool)>,
) -> Result<Expr, BvComputeBlastError> {
    if assigned.len() == inputs.len() {
        let pos = lits
            .iter()
            .position(|&l| eval_lit_under_inputs(refl, l, assigned) == Some(true))
            .ok_or(BvComputeBlastError::NotAGateTautology { clause: clause_id })?;
        // ground props (inputs substituted) so the injected chain type is ground.
        let ground = ground_clause_props(refl, lits, assigned);
        let refl_true = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![u1()]),
            [bool_ty(), btrue()],
        );
        return Ok(inject_clause_or(&ground, pos, refl_true));
    }

    let var = inputs[assigned.len()];
    let sig_term = refl.term[var as usize].clone();
    // motive : fun (w : Bool) => clauseOr-shape over props with input `var := w`.
    let motive = {
        let body = clause_or_chain_subst(refl, lits, assigned, var, Expr::bvar(0));
        Expr::lam(BinderInfo::Default, bool_ty(), body)
    };
    assigned.push((var, false));
    let fb = gate_split(refl, clause_id, lits, inputs, assigned)?;
    assigned.pop();
    assigned.push((var, true));
    let tb = gate_split(refl, clause_id, lits, inputs, assigned)?;
    assigned.pop();
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    Ok(Expr::apps(bool_rec, [motive, fb, tb, sig_term]))
}

/// Evaluate literal `l` under the FULL input assignment `assigned`, by substituting the
/// assigned input signals into the literal's reflected term (the SAME `subst_signals`
/// the kernel sees) and folding the now-ground gate term to a `bool`. Because every
/// gate input is assigned, the substituted term contains only `Bool` constants and gate
/// operators — so this exactly mirrors the kernel's definitional reduction (no fragile
/// atom-by-term matching). Returns `None` if a non-constant atom survives (the term was
/// not fully ground — a malformed clause), which `gate_split` treats as "not satisfied".
fn eval_lit_under_inputs(refl: &Reflection, l: Lit, assigned: &[(u32, bool)]) -> Option<bool> {
    let ground = subst_signals(refl, refl.term[l.var as usize].clone(), assigned, None);
    let v = fold_ground_bool(&ground)?;
    Some(if l.neg { !v } else { v })
}

/// Fold a fully-ground reflected `Bool` expr (only `Bool` constants + the BV4 gate
/// operators) to a concrete `bool`. Returns `None` if a non-constant atom remains.
fn fold_ground_bool(e: &Expr) -> Option<bool> {
    use clean_kernel::ExprKind;
    let head = e.get_app_fn();
    let args = e.get_app_args();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    let n = name.to_string();
    match (n.as_str(), args.len()) {
        ("Bool.true", 0) => Some(true),
        ("Bool.false", 0) => Some(false),
        (s, 3) if s == cnames::XOR3 => Some(
            fold_ground_bool(args[0])? ^ fold_ground_bool(args[1])? ^ fold_ground_bool(args[2])?,
        ),
        (s, 3) if s == cnames::MAJ => {
            let (x, y, z) = (
                fold_ground_bool(args[0])?,
                fold_ground_bool(args[1])?,
                fold_ground_bool(args[2])?,
            );
            Some((x & y) | (x & z) | (y & z))
        }
        ("Bool.not", 1) => Some(!fold_ground_bool(args[0])?),
        ("Bool.xor", 2) => Some(fold_ground_bool(args[0])? ^ fold_ground_bool(args[1])?),
        ("Bool.and", 2) => Some(fold_ground_bool(args[0])? && fold_ground_bool(args[1])?),
        ("Bool.or", 2) => Some(fold_ground_bool(args[0])? || fold_ground_bool(args[1])?),
        _ => None,
    }
}

/// `clauseOr`-shaped chain type with `assigned` input signals substituted to ground
/// and the splitting input `split_var` substituted to `subst`.
fn clause_or_chain_subst(
    refl: &Reflection,
    lits: &[Lit],
    assigned: &[(u32, bool)],
    split_var: u32,
    subst: Expr,
) -> Expr {
    let props: Vec<Expr> = lits
        .iter()
        .map(|&l| {
            let b = lit_bool(refl, l);
            let b = subst_signals(refl, b, assigned, Some((split_var, subst.clone())));
            holds(b)
        })
        .collect();
    clause_or_type_props(&props)
}

/// Ground `clauseOr` prop list (all assigned input signals substituted).
fn ground_clause_props(refl: &Reflection, lits: &[Lit], assigned: &[(u32, bool)]) -> Vec<Expr> {
    lits.iter()
        .map(|&l| {
            let b = lit_bool(refl, l);
            let b = subst_signals(refl, b, assigned, None);
            holds(b)
        })
        .collect()
}

/// Substitute reflected gate-INPUT signal terms (`refl.term[var]`) inside a reflected
/// `Bool` expr to ground `Bool.true`/`Bool.false` (or, for the splitting input, to
/// `subst`). An input signal can be syntactically nested inside the gate OUTPUT term
/// of the same clause; replacing in outermost-first order keeps the substitution
/// well-defined.
fn subst_signals(
    refl: &Reflection,
    e: Expr,
    assigned: &[(u32, bool)],
    split: Option<(u32, Expr)>,
) -> Expr {
    let mut reps: Vec<(Expr, Expr)> = assigned
        .iter()
        .map(|&(var, v)| {
            (
                refl.term[var as usize].clone(),
                if v { btrue() } else { bfalse() },
            )
        })
        .collect();
    if let Some((var, to)) = split {
        reps.push((refl.term[var as usize].clone(), to));
    }
    reps.sort_by_key(|r| std::cmp::Reverse(node_count(&r.0)));
    let mut out = e;
    for (from, to) in &reps {
        out = replace_subterm(&out, from, to);
    }
    out
}

/// Number of `Expr` nodes (used only to order signal substitutions outermost-first).
fn node_count(e: &Expr) -> usize {
    use clean_kernel::ExprKind;
    1 + match e.kind() {
        ExprKind::App(f, x) => node_count(f) + node_count(x),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => node_count(ty) + node_count(body),
        _ => 0,
    }
}

fn replace_subterm(e: &Expr, from: &Expr, to: &Expr) -> Expr {
    if e == from {
        return to.clone();
    }
    use clean_kernel::ExprKind;
    match e.kind() {
        ExprKind::App(f, x) => {
            Expr::app(replace_subterm(f, from, to), replace_subterm(x, from, to))
        }
        ExprKind::Lam(bd, ty, body) => Expr::lam(
            *bd,
            replace_subterm(ty, from, to),
            replace_subterm(body, from, to),
        ),
        ExprKind::Pi(bd, ty, body) => Expr::pi(
            *bd,
            replace_subterm(ty, from, to),
            replace_subterm(body, from, to),
        ),
        _ => e.clone(),
    }
}

// ── disequality clause: clauseOr H diseq from Not (bvEq lhs rhs) ────────────────

/// `Clean.BV{N}.bit{k} operand` for the layer width `nm`.
fn bit_of(nm: BvNames, operand: &Expr, k: u32) -> Expr {
    Expr::app(Expr::const_str(&nm.bit(k)), operand.clone())
}
fn bnot(x: Expr) -> Expr {
    Expr::app(Expr::const_str("Bool.not"), x)
}

/// Prove `clauseOr H (¬e_0 ∨ … ∨ ¬e_{n-1})` from `h : Not (bvEq lhs rhs)`.
///
/// `boolEm`-case each bit-equality var `e_i`'s reflected `Bool` term `t_{e_i} =
/// xnor(LhsOut_i, RhsOut_i)`: a `false` leaf makes `¬e_i` `Holds` (`notFalseImpTrue`)
/// → inject; the all-`true` path yields each per-bit equality via `xnorTrueImpEq`
/// over the bit-blast OUTPUT terms (`LhsOut_i`/`RhsOut_i`, def-eq to `bit i lhs` /
/// `bit i rhs`), assembling `bvEq lhs rhs` to contradict `h`.
#[allow(clippy::too_many_arguments)]
fn prove_diseq_clause_or(
    refl: &Reflection,
    proof: &BvBlastProof,
    fresh: &Fresh,
    lhs: &Expr,
    rhs: &Expr,
    h_goal: &Expr,
    diseq_lits: &[Lit],
) -> Result<Expr, BvComputeBlastError> {
    // per-bit: (BitEq index, LhsOut term, RhsOut term).
    let mut per_bit: Vec<(u32, Expr, Expr)> = Vec::with_capacity(diseq_lits.len());
    for l in diseq_lits {
        let bit = refl
            .bit_eq_bit
            .get(l.var as usize)
            .copied()
            .flatten()
            .ok_or_else(|| {
                BvComputeBlastError::InvalidProof("diseq literal is not a BitEq var".into())
            })?;
        let lemma = proof
            .bit_lemmas
            .iter()
            .find(|lm| lm.out == l.var && matches!(lm.kind, BitLemmaKind::XnorEq))
            .ok_or_else(|| {
                BvComputeBlastError::InvalidProof(format!("BitEq var {} has no XnorEq", l.var))
            })?;
        if lemma.ins.len() != 2 {
            return Err(BvComputeBlastError::InvalidProof(format!(
                "XnorEq lemma var {} arity {}",
                l.var,
                lemma.ins.len()
            )));
        }
        let lhs_out = refl.term[lemma.ins[0] as usize].clone();
        let rhs_out = refl.term[lemma.ins[1] as usize].clone();
        per_bit.push((bit, lhs_out, rhs_out));
    }
    let clause_props_v: Vec<Expr> = diseq_lits
        .iter()
        .map(|&l| holds(lit_bool(refl, l)))
        .collect();
    diseq_go(
        refl,
        fresh,
        lhs,
        rhs,
        h_goal,
        diseq_lits,
        &per_bit,
        &clause_props_v,
        0,
        &mut Vec::new(),
    )
}

#[allow(clippy::too_many_arguments)]
fn diseq_go(
    refl: &Reflection,
    fresh: &Fresh,
    lhs: &Expr,
    rhs: &Expr,
    h_goal: &Expr,
    diseq_lits: &[Lit],
    per_bit: &[(u32, Expr, Expr)],
    clause_props_v: &[Expr],
    i: usize,
    eqs: &mut Vec<(u32, Expr)>,
) -> Result<Expr, BvComputeBlastError> {
    let n = diseq_lits.len();
    let var_i = diseq_lits[i].var;
    let (bit_i, ref lhs_bit, ref rhs_bit) = per_bit[i];
    let t_e = refl.term[var_i as usize].clone(); // xnor(LhsOut_i, RhsOut_i)
    let lhs_bit = lhs_bit.clone();
    let rhs_bit = rhs_bit.clone();

    let em = Expr::app(Expr::const_str(cnames::BOOL_EM), t_e.clone());
    let p_true = holds(t_e.clone());
    let p_false = eq_bool(t_e.clone(), bfalse());

    // suffix clauseOr-chain type for clause_props_v[i..]
    let suffix_type = clause_or_type_props(&clause_props_v[i..]);
    // motive : fun (_ : Or p_true p_false) => suffix_type
    let motive = {
        Expr::lam(
            BinderInfo::Default,
            or_t(p_true.clone(), p_false.clone()),
            suffix_type.clone(),
        )
    };

    // true branch: xnorTrueImpEq → lhs_bit = rhs_bit; recurse / contradict.
    let (htrue_id, htrue) = fresh.fvar();
    let eq_i = Expr::apps(
        Expr::const_str(cnames::XNOR_TRUE_IMP_EQ),
        [lhs_bit.clone(), rhs_bit.clone(), htrue.clone()],
    );
    eqs.push((bit_i, eq_i));
    let true_inner = if i + 1 == n {
        let andchain = build_bv_eq_andchain(refl.nm, lhs, rhs, eqs)?;
        let false_pf = Expr::app(h_goal.clone(), andchain);
        // suffix_type here = Or (clause_props_v[n-1]) False ; inject False via False.elim.
        Expr::apps(
            Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            [suffix_type.clone(), false_pf],
        )
    } else {
        let rest = diseq_go(
            refl,
            fresh,
            lhs,
            rhs,
            h_goal,
            diseq_lits,
            per_bit,
            clause_props_v,
            i + 1,
            eqs,
        )?;
        let head = clause_props_v[i].clone();
        let tail = clause_or_type_props(&clause_props_v[i + 1..]);
        or_inr(head, tail, rest)
    };
    eqs.pop();
    let true_branch = Expr::lam(
        BinderInfo::Default,
        p_true.clone(),
        true_inner.abstract_fvar(htrue_id),
    );

    // false branch: notFalseImpTrue → Holds(¬e_i); Or.inl.
    let (hfalse_id, hfalse) = fresh.fvar();
    let neg_holds = Expr::apps(
        Expr::const_str(cnames::NOT_FALSE_IMP_TRUE),
        [t_e.clone(), hfalse.clone()],
    );
    let head = clause_props_v[i].clone();
    let tail = clause_or_type_props(&clause_props_v[i + 1..]);
    let false_inner = or_inl(head, tail, neg_holds);
    let false_branch = Expr::lam(
        BinderInfo::Default,
        p_false.clone(),
        false_inner.abstract_fvar(hfalse_id),
    );

    // Or.rec p_true p_false motive true_branch false_branch em
    Ok(Expr::apps(
        Expr::const_(Name::from_string("Or.rec"), vec![]),
        [p_true, p_false, motive, true_branch, false_branch, em],
    ))
}

/// Assemble `bvEq lhs rhs`'s definitional `And`-chain from per-bit equality proofs.
fn build_bv_eq_andchain(
    nm: BvNames,
    lhs: &Expr,
    rhs: &Expr,
    eqs: &[(u32, Expr)],
) -> Result<Expr, BvComputeBlastError> {
    let width = eqs.len() as u32;
    let proof_of = |bit: u32| -> Result<Expr, BvComputeBlastError> {
        eqs.iter()
            .find(|(b, _)| *b == bit)
            .map(|(_, p)| p.clone())
            .ok_or(BvComputeBlastError::InvalidProof(format!(
                "missing per-bit equality for bit {bit}"
            )))
    };
    let prop_of = |bit: u32| eq_bool(bit_of(nm, lhs, bit), bit_of(nm, rhs, bit));
    let last = width - 1;
    let mut acc_proof = proof_of(last)?;
    let mut acc_ty = prop_of(last);
    for bit in (0..last).rev() {
        let head_ty = prop_of(bit);
        let head_proof = proof_of(bit)?;
        acc_proof = Expr::apps(
            Expr::const_(Name::from_string("And.intro"), vec![]),
            [head_ty.clone(), acc_ty.clone(), head_proof, acc_proof],
        );
        acc_ty = and_t(head_ty, acc_ty);
    }
    Ok(acc_proof)
}

// ── allSat assembly + top-level lowering bridge ─────────────────────────────────

/// Encode one clause's literals as a kernel `List Nat` (matching the BigNat-literal
/// `encode_clauses_lit` the `checkRefutes3` bridge feeds to `certify_unsat3_by_reflection`).
///
/// Literals are BigNat LITERALS ([`encode_lit_lit`]) so the `cs` this encoding-fidelity
/// `allSat H cs` proof is about is bit-for-bit the same `cs` the trie checker reduces
/// (and the `Unsat cs` it produces). If these two `cs` representations diverged (one
/// unary, one BigNat) the `Unsat cs → allSat H cs → False` application would still
/// type-check by def-eq, but only after an EXPENSIVE unary⇄BigNat reduction of the whole
/// clause DB — defeating the point of the compact representation.
fn encode_clause_list(lits: &[Lit]) -> Expr {
    let mut acc = list_nil_nat();
    for l in lits.iter().rev() {
        acc = list_cons_nat(encode_lit_lit(l.var, l.neg), acc);
    }
    acc
}

/// Encode the full clause DB as a kernel `List (List Nat)`.
fn encode_clause_db(proof: &BvBlastProof) -> Expr {
    let mut acc = list_nil_ll();
    for c in proof.clauses.iter().rev() {
        acc = list_cons_ll(encode_clause_list(&c.lits), acc);
    }
    acc
}

/// Build `allSat H db` as the right-folded `And` of the per-clause `clauseOr H c`
/// proofs, ending in `True.intro`. `clause_proofs[i]` proves `clauseOr H clauses[i]`.
fn build_all_sat(h: &Expr, proof: &BvBlastProof, clause_proofs: &[Expr]) -> Expr {
    // allSat H [c0,..,c_{m-1}] ≡ And (clauseOr H c0) (And (clauseOr H c1) (... True)).
    let n = proof.clauses.len();
    let mut acc = Expr::const_str("True.intro");
    // suffix type at depth d: allSat-body over clauses[d..]; build And.intro outward.
    // We need the And types: head_d = clauseOr H clauses[d]; tail_d = And-chain of [d+1..] ++ True.
    // Precompute clauseOr types.
    let or_types: Vec<Expr> = proof
        .clauses
        .iter()
        .map(|c| clause_or(h, encode_clause_list(&c.lits)))
        .collect();
    // tail type at depth d (the `allSat` of clauses[d..]).
    let mut tail_types: Vec<Expr> = vec![Expr::const_str("True"); n + 1];
    for d in (0..n).rev() {
        tail_types[d] = and_t(or_types[d].clone(), tail_types[d + 1].clone());
    }
    for d in (0..n).rev() {
        acc = Expr::apps(
            Expr::const_(Name::from_string("And.intro"), vec![]),
            [
                or_types[d].clone(),
                tail_types[d + 1].clone(),
                clause_proofs[d].clone(),
                acc,
            ],
        );
    }
    acc
}

/// Build the FULLY zero-trust lowering certificate `bvEq lhs rhs` from the
/// solver-backed width-4 commutativity [`BvBlastProof`] and the proved `Unsat`
/// reflection cert.
///
/// `lhs`/`rhs` are the BV4 sides (`bvAdd a b`, `bvAdd b a`); `operand_a`/`operand_b`
/// the symbolic `Clean.BV4`. The returned [`LoweringBridge`] holds a kernel term of
/// type `bvEq lhs rhs`, already KERNEL-TYPE-CHECKED.
///
/// # Errors
/// [`BvComputeBlastError`] if the producer validates wrong, the obligation is not
/// the solver-backed swapped one, a gate clause is not a tautology, or the kernel
/// rejects the assembled term.
pub fn certify_lowering_by_reflection(
    env: &mut Environment,
    proof: &BvBlastProof,
    lhs: &Expr,
    rhs: &Expr,
    operand_a: &Expr,
    operand_b: &Expr,
    name_prefix: &str,
) -> Result<LoweringBridge, BvComputeBlastError> {
    proof
        .validate()
        .map_err(|e| BvComputeBlastError::InvalidProof(format!("{e}")))?;
    if proof.obligation.is_identical() {
        return Err(BvComputeBlastError::NotSolverBacked);
    }

    // SOUNDNESS-SAFE heartbeat lift. The reflection `Unsat` cert (the `_unsat`
    // Definition below) forces the kernel to reduce `Clean.Res.checkRefutes <clauses>
    // <refutation>` over the proof data; that linear ι-reduction overshoots the kernel
    // 2_000_000 default heartbeat at bit-width ≥ 6, where `whnf` BAILS fail-CLOSED
    // (returns the stuck, unreduced term → `Eq.refl` rejected). Lifting the heartbeat
    // only lets a VALID refutation COMPLETE; a wrong refutation still reduces to
    // `Bool.false` and is rejected, so this can never accept an invalid refutation.
    // Default to unlimited (matching the real Lean kernel); honor an explicit caller
    // override of `maxHeartbeats`. Every `add_decl` type-check below reads this option;
    // the explicit `check_type`s in this path go through `reflection_tc` likewise.
    if env.get_option("maxHeartbeats").is_none() {
        env.set_option("maxHeartbeats".to_string(), Some("0".to_string()));
    }

    let refl = build_reflection(proof, operand_a, operand_b)?;
    let fresh = Fresh::new();

    // f_ab : Nat → Bool and the induced model H := boolModel f_ab. `f_ab` is a deep
    // `Nat.rec` ladder embedding ALL 28 reflected gate trees, so it is registered as a
    // named `Definition <prefix>_fab` and referenced by const everywhere. This keeps the
    // model `H` opaque-by-name in every `clauseOr H c` / `allSat H cs` type: def-eq of
    // `H` across the gate lemmas and the final goal is then an O(1) name comparison
    // instead of reducing two copies of the giant ladder (the real >100 GB driver).
    let f_ab_term = build_var_table_fn(&refl, &fresh);
    let fab_name = Name::from_string(&format!("{name_prefix}_fab"));
    env.add_decl(clean_kernel::Declaration::Definition {
        name: fab_name.clone(),
        level_params: vec![],
        type_: Expr::arrow(nat_ty(), bool_ty()),
        value: f_ab_term.clone(),
        is_reducible: false,
    })
    .map_err(|e| BvComputeBlastError::InvalidProof(format!("f_ab table rejected: {e:?}")))?;
    let f_ab = Expr::const_str(&fab_name.to_string());
    let h_model = bool_model(&f_ab);

    // bvEq goal + negated-goal fvar.
    let bv_eq_goal = clean_kernel::bitvec_compute::bv_eq_for(refl.nm, lhs.clone(), rhs.clone());
    let not_goal = Expr::app(Expr::const_str("Not"), bv_eq_goal.clone());
    let (h_id, h_goal) = fresh.fvar();

    // Per-clause clauseOr proofs. Each GATE clause is closed (no fvars) and is
    // registered as its own `Definition <prefix>_gate_<id> : clauseOr H c` so the
    // kernel `check_type`s it in ISOLATION — the `allSat` chain then references it by
    // name and the kernel does NOT re-reduce the (heavy) ripple-carry gate trees. This
    // bounds the peak memory of the fidelity check to one clause at a time instead of
    // reducing all 130 gate trees inside a single monolithic term (which peaked >100
    // GB). The disequality clause is open in the negated-goal fvar, so it stays inline.
    let mut clause_proofs: Vec<Expr> = Vec::with_capacity(proof.clauses.len());
    let mut gate_clauses_proved = 0usize;
    for cl in &proof.clauses {
        let p = match cl.provenance {
            ClauseProvenance::BitLemmaCnf { lemma } => {
                let Some(bl) = proof.bit_lemmas.get(lemma as usize) else {
                    return Err(BvComputeBlastError::MissingLemma {
                        clause: cl.id,
                        lemma,
                    });
                };
                gate_clauses_proved += 1;
                let proof_term = prove_gate_clause_or(&refl, cl.id, &cl.lits, &bl.ins)?;
                let gate_ty = clause_or(&h_model, encode_clause_list(&cl.lits));
                let gate_name = Name::from_string(&format!("{name_prefix}_gate_{}", cl.id));
                env.add_decl(clean_kernel::Declaration::Definition {
                    name: gate_name.clone(),
                    level_params: vec![],
                    type_: gate_ty,
                    value: proof_term,
                    is_reducible: false,
                })
                .map_err(|e| {
                    BvComputeBlastError::InvalidProof(format!(
                        "gate clause {} proof rejected: {e:?}",
                        cl.id
                    ))
                })?;
                Expr::const_str(&gate_name.to_string())
            }
            ClauseProvenance::Disequality => {
                // The disequality clause is open in the negated-goal fvar `h_goal`; its
                // proof routes through `xnorTrueImpEq` over the DEEP bit-blast output
                // trees and is the single heaviest reduction. Register it as its own
                // `Definition <prefix>_diseq : Not(bvEq) → clauseOr H diseq` so the
                // kernel checks that reduction ONCE in isolation; the `allSat` spine
                // then references `<prefix>_diseq h` by name without re-reducing it.
                let diseq_body =
                    prove_diseq_clause_or(&refl, proof, &fresh, lhs, rhs, &h_goal, &cl.lits)?;
                let diseq_under_h = Expr::lam(
                    BinderInfo::Default,
                    not_goal.clone(),
                    diseq_body.abstract_fvar(h_id),
                );
                let diseq_ty = clause_or(&h_model, encode_clause_list(&cl.lits));
                let diseq_def_ty = Expr::arrow(not_goal.clone(), diseq_ty);
                let diseq_name = Name::from_string(&format!("{name_prefix}_diseq"));
                env.add_decl(clean_kernel::Declaration::Definition {
                    name: diseq_name.clone(),
                    level_params: vec![],
                    type_: diseq_def_ty,
                    value: diseq_under_h,
                    is_reducible: false,
                })
                .map_err(|e| {
                    BvComputeBlastError::InvalidProof(format!(
                        "disequality clause proof rejected: {e:?}"
                    ))
                })?;
                Expr::app(Expr::const_str(&diseq_name.to_string()), h_goal.clone())
            }
        };
        clause_proofs.push(p);
    }

    // The encoding-fidelity proof, as a Definition `<prefix>_allSat : Not(bvEq) →
    // allSat H cs`. Registering it CHECKS the heavy reduction ONCE; later references
    // are by name (the kernel trusts a checked decl's type and does not re-reduce it).
    // With every gate clause AND the disequality clause pre-checked as named lemmas,
    // this final assembly only has to re-check the cheap `And.intro` spine.
    let all_sat_body = build_all_sat(&h_model, proof, &clause_proofs);
    let all_sat_under_h = Expr::lam(
        BinderInfo::Default,
        not_goal.clone(),
        all_sat_body.abstract_fvar(h_id),
    );
    let all_sat_ty = all_sat(&h_model, encode_clause_db(proof));
    let all_sat_def_ty = Expr::arrow(not_goal.clone(), all_sat_ty);
    let all_sat_name = Name::from_string(&format!("{name_prefix}_allSat"));
    env.add_decl(clean_kernel::Declaration::Definition {
        name: all_sat_name.clone(),
        level_params: vec![],
        type_: all_sat_def_ty,
        value: all_sat_under_h,
        is_reducible: false,
    })
    .map_err(|e| {
        BvComputeBlastError::InvalidProof(format!("allSat fidelity proof rejected: {e:?}"))
    })?;

    // The Unsat term (proved, zero-trust), registered as a Definition so its (heavy)
    // type is checked ONCE; later referenced by name. Discharged through the PROVEN
    // SUB-QUADRATIC `checkRefutes3_sound` (trie-backed `checkRefutes3 (initialTrie cs)
    // (listLen cs) steps`) instead of the O(steps²) `checkRefutes_sound` — same `Unsat
    // cs` conclusion (and same `cs` term, so the encoding-fidelity `allSat H cs`
    // discharge below is unchanged), but the resolution-checker reduction is
    // sub-quadratic in the step count.
    let (unsat_term, unsat_goal) =
        super::bv_blast_reflection::certify_unsat3_by_reflection(env, proof)
            .map_err(|e| BvComputeBlastError::InvalidProof(format!("Unsat cert: {e:?}")))?;
    let unsat_name = Name::from_string(&format!("{name_prefix}_unsat"));
    env.add_decl(clean_kernel::Declaration::Definition {
        name: unsat_name.clone(),
        level_params: vec![],
        type_: unsat_goal,
        value: unsat_term,
        is_reducible: false,
    })
    .map_err(|e| BvComputeBlastError::InvalidProof(format!("Unsat cert rejected: {e:?}")))?;

    // Assemble: byContradiction (fun h => <unsat> H cons excl (<allSat> h)) : bvEq.
    let cons = Expr::app(Expr::const_str(mnames::BOOL_MODEL_CONSISTENT), f_ab.clone());
    let excl = Expr::app(Expr::const_str(mnames::BOOL_MODEL_EXCLUSIVE), f_ab.clone());
    let (h2_id, h2) = fresh.fvar();
    let all_sat_app = Expr::app(Expr::const_str(&all_sat_name.to_string()), h2.clone());
    // Unsat cs ≡ (H) → resConsistent H → resExclusive H → allSat H cs → False.
    let false_term = Expr::apps(
        Expr::const_str(&unsat_name.to_string()),
        [h_model.clone(), cons, excl, all_sat_app],
    );
    let nn_term = Expr::lam(
        BinderInfo::Default,
        not_goal.clone(),
        false_term.abstract_fvar(h2_id),
    );
    let bv_eq_term = Expr::apps(
        Expr::const_str("Classical.byContradiction"),
        [bv_eq_goal.clone(), nn_term],
    );

    // Kernel-check the assembled term inhabits the goal (heartbeat governed by env).
    // NOTE: deliberately uses the DEFAULT cache budget (not the step-scaled one). This
    // final check re-reduces the WHOLE assembled cert (the `allSat` fidelity chain AND
    // the `checkRefutes3` `Unsat` term) in one `check_type`, so its working set is the
    // UNION of every sub-reduction's — at a 1M cache that retains ~118 GB of huge cert
    // subterms (vs ~8 GB for the isolated `Unsat` reduction). The step-scaled budget is
    // applied only to the ISOLATED `certify3`/`certify_unsat3` reductions, where it pays
    // off without the memory blow-up. (Speeding up this final re-reduction without the
    // memory cost would need cache SHARING across the certify_unsat3 + assembly checks —
    // a structural change; tracked as the next perf step.)
    let tc = super::bv_blast_reflection::reflection_tc_sized(env, 0);
    tc.check_type(&bv_eq_term, &bv_eq_goal).map_err(|e| {
        BvComputeBlastError::InvalidProof(format!("assembled lowering cert rejected: {e:?}"))
    })?;

    Ok(LoweringBridge {
        bv_eq_term,
        bv_eq_goal,
        gate_clauses_proved,
    })
}

/// Build + kernel-check ONLY the `allSat (boolModel f_ab) <clauses>` fidelity proof
/// (the encoding-fidelity half), returning the proof term and its checked type.
/// Used to validate / time the bridge independently of the (heavy) `Unsat` cert.
///
/// Like [`certify_lowering_by_reflection`], each gate clause is registered as its own
/// pre-checked `Definition <prefix>_gate_<id>` so the final `allSat` `check_type` stays
/// tractable (it does NOT reduce all 130 ripple-carry gate trees in one term).
///
/// # Errors
/// [`BvComputeBlastError`] if a clause proof is malformed or the kernel rejects the
/// assembled `allSat` term (open in the negated-goal fvar for the disequality clause).
pub fn build_and_check_all_sat(
    env: &mut Environment,
    proof: &BvBlastProof,
    lhs: &Expr,
    rhs: &Expr,
    operand_a: &Expr,
    operand_b: &Expr,
    name_prefix: &str,
) -> Result<(Expr, Expr, FVarId), BvComputeBlastError> {
    proof
        .validate()
        .map_err(|e| BvComputeBlastError::InvalidProof(format!("{e}")))?;
    let refl = build_reflection(proof, operand_a, operand_b)?;
    let fresh = Fresh::new();
    // Register `f_ab` as a named const so `H` is opaque-by-name (see the main path).
    let f_ab_term = build_var_table_fn(&refl, &fresh);
    let fab_name = Name::from_string(&format!("{name_prefix}_fab"));
    env.add_decl(clean_kernel::Declaration::Definition {
        name: fab_name.clone(),
        level_params: vec![],
        type_: Expr::arrow(nat_ty(), bool_ty()),
        value: f_ab_term,
        is_reducible: false,
    })
    .map_err(|e| BvComputeBlastError::InvalidProof(format!("f_ab table rejected: {e:?}")))?;
    let f_ab = Expr::const_str(&fab_name.to_string());
    let h_model = bool_model(&f_ab);
    let bv_eq_goal = clean_kernel::bitvec_compute::bv_eq_for(refl.nm, lhs.clone(), rhs.clone());
    let not_goal = Expr::app(Expr::const_str("Not"), bv_eq_goal);
    let (h_id, h_goal) = fresh.fvar();

    let mut clause_proofs: Vec<Expr> = Vec::with_capacity(proof.clauses.len());
    for cl in &proof.clauses {
        let p = match cl.provenance {
            ClauseProvenance::BitLemmaCnf { lemma } => {
                let Some(bl) = proof.bit_lemmas.get(lemma as usize) else {
                    return Err(BvComputeBlastError::MissingLemma {
                        clause: cl.id,
                        lemma,
                    });
                };
                let proof_term = prove_gate_clause_or(&refl, cl.id, &cl.lits, &bl.ins)?;
                let gate_ty = clause_or(&h_model, encode_clause_list(&cl.lits));
                let gate_name = Name::from_string(&format!("{name_prefix}_gate_{}", cl.id));
                env.add_decl(clean_kernel::Declaration::Definition {
                    name: gate_name.clone(),
                    level_params: vec![],
                    type_: gate_ty,
                    value: proof_term,
                    is_reducible: false,
                })
                .map_err(|e| {
                    BvComputeBlastError::InvalidProof(format!(
                        "gate clause {} proof rejected: {e:?}",
                        cl.id
                    ))
                })?;
                Expr::const_str(&gate_name.to_string())
            }
            ClauseProvenance::Disequality => {
                // Register the (heavy) disequality clause as its own h-abstracted
                // Definition so its `xnorTrueImpEq`-over-deep-trees reduction is checked
                // ONCE here, not re-reduced inside the final `allSat` check.
                let diseq_body =
                    prove_diseq_clause_or(&refl, proof, &fresh, lhs, rhs, &h_goal, &cl.lits)?;
                let diseq_under_h = Expr::lam(
                    BinderInfo::Default,
                    not_goal.clone(),
                    diseq_body.abstract_fvar(h_id),
                );
                let diseq_ty = clause_or(&h_model, encode_clause_list(&cl.lits));
                let diseq_def_ty = Expr::arrow(not_goal.clone(), diseq_ty);
                let diseq_name = Name::from_string(&format!("{name_prefix}_diseq"));
                env.add_decl(clean_kernel::Declaration::Definition {
                    name: diseq_name.clone(),
                    level_params: vec![],
                    type_: diseq_def_ty,
                    value: diseq_under_h,
                    is_reducible: false,
                })
                .map_err(|e| {
                    BvComputeBlastError::InvalidProof(format!(
                        "disequality clause proof rejected: {e:?}"
                    ))
                })?;
                Expr::app(Expr::const_str(&diseq_name.to_string()), h_goal.clone())
            }
        };
        clause_proofs.push(p);
    }
    let all_sat_proof = build_all_sat(&h_model, proof, &clause_proofs);
    let all_sat_ty = all_sat(&h_model, encode_clause_db(proof));

    // Check in a context binding the open negated-goal fvar.
    let mut ctx = clean_kernel::LocalContext::new();
    ctx.push_with_id(
        h_id,
        Name::from_string("h_neg"),
        not_goal,
        BinderInfo::Default,
    );
    let mut tc = TypeChecker::with_context(env, ctx);
    // Heartbeat governed by env (default unlimited for this reflection path); see
    // `bv_blast_reflection::reflection_tc_sized`. The allSat fidelity reduction is heavy
    // at wider widths and must not silently BAIL fail-closed under the 2M default.
    let limit = match env.get_option("maxHeartbeats") {
        Some(Some(s)) => s.parse::<u32>().unwrap_or(0),
        _ => 0,
    };
    tc.set_heartbeat_limit(limit);
    // Default cache budget: this allSat-fidelity reduction is part of the heavy e2e
    // working set, and (like the final assembly) bumping its cache multiplies peak
    // memory at width 32 without a commensurate win. The step-scaled budget is reserved
    // for the isolated `checkRefutes3` `Unsat`-cert reductions (`certify3`/`certify_unsat3`).
    tc.check_type(&all_sat_proof, &all_sat_ty).map_err(|e| {
        BvComputeBlastError::InvalidProof(format!("allSat fidelity proof rejected: {e:?}"))
    })?;
    Ok((all_sat_proof, all_sat_ty, h_id))
}

#[cfg(test)]
#[path = "tests_bv_lowering_bridge.rs"]
mod tests;

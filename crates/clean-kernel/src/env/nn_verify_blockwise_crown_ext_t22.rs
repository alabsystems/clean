// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T22 `LayerNorm.zonotope_generators_reset` — MASQUERADE RETIRED via a
//! FAITHFUL MATRIX RESTATEMENT (Branch B, supersedes the #3590 Branch A
//! honest demotion).
//!
//! **Status:** Contains 2 `Declaration::Theorem` entries
//! (`NNVerify.LayerNorm.zonotope_generators_reset` — diagonal-entry
//! equation; `NNVerify.LayerNorm.zonotope_generators_offdiagonal` — the
//! off-diagonal-is-zero companion) and 1 supporting reducible
//! `Declaration::Definition` carrier
//! (`NNVerify.LayerNorm.generators_after_ln`). All three GENUINELY consume
//! the `k` input generator columns; none reduces to `n = n` / `Eq.refl`
//! over a `k`-discarding carrier. The former axiom is RETIRED.
//!
//! Split out of `nn_verify_blockwise_crown_ext.rs` (#3495) to stay under
//! the 500-line file-size cap and to localise the MASQUERADE history so
//! future audits can see the before/after in one place.
//!
//! ### MASQUERADE history (carrier was `Nat -> Nat -> Nat`)
//!
//! The 2026-04-19 `clean-native.mathverse` shard audit
//! (`reports/audit/2026-04-19-clean-native-shard-audit.md`, entry 10)
//! flagged T22 as trivial-by-construction. The original carrier
//! `LayerNorm.generators_after_ln : Nat -> Nat -> Nat` returned `n`
//! REGARDLESS of `k` (`fun n _ => n`, later cosmetically wrapped in a
//! `Nat.rec` whose step branch discarded both `_m` and `_ih`), so the
//! companion theorem `generators_after_ln n k = n` reduced to `n = n`,
//! closed by `Eq.refl` — a textbook M2+M3+M4 MASQUERADE
//! (`designs/2026-04-19-demasquerade-cxxx-pattern.md`):
//!
//! - **M2** (argument-discarding carrier): `k` is provably irrelevant —
//!   ANY `Nat -> Nat -> Nat` carrier that returns `n` is cosmetic.
//! - **M3** (cosmetic `Nat.rec` wrapper): the structural recursion carried
//!   no semantic dependency on `k`.
//! - **M4** (`Eq.refl` root): the induction hypothesis was bound and
//!   ignored; both constructor branches collapsed to `n = n`.
//!
//! #3590 Branch A demoted the theorem to a body-less `Declaration::Axiom`
//! and co-demoted the carrier to `Declaration::Opaque` (same body, only the
//! declaration kind flipped). That closed the alias-collapse loophole but
//! left a body-less axiom in the trusted base — the count was honest but
//! the content was still absent.
//!
//! ### Branch B retirement (FAITHFUL MATRIX RESTATEMENT, this file)
//!
//! The carrier is now the GENERATOR MATRIX produced by LayerNorm, not a
//! `Nat`. LayerNorm destroys the zonotope correlation structure and
//! projects onto the AXIS-ALIGNED BOX (interval hull) of the input. The
//! box's generator matrix is the `n x n` DIAGONAL matrix `diag(radius_i)`,
//! where
//!
//! ```text
//! radius_i = Fin.sum k (fun (j : Fin k) => Rat.abs (z.generators i j))
//! ```
//!
//! is the SAME per-row L1 radius that the faithful `NNVerify.Zonotope.to_ibp`
//! computes (`nn_verify_zonotope_to_ibp_faithful`). The radius GENUINELY
//! consumes all `k` input generator columns, so the carrier is NOT
//! argument-discarding:
//!
//! ```text
//! generators_after_ln (n k : Nat) (z : Zonotope n k) : NNMat n n :=
//!   fun (i i' : Fin n) =>
//!     @Decidable.rec (Eq (Fin n) i i') (fun _ => Rat)
//!       (isFalse := fun _ => Rat.zero)          -- off-diagonal: 0
//!       (isTrue  := fun _ => radius_i)           -- diagonal: per-row L1 radius
//!       (instDecidableEqFin n i i')
//! ```
//!
//! The output has `n` columns BY TYPE (`NNMat n n`), so the historical
//! "generator count resets to n" claim is now a CONSEQUENCE of construction
//! (the type), not a separately-asserted equation. The two restated
//! theorems characterise the construction as the diagonal radius box:
//!
//! 1. **`zonotope_generators_reset`** (diagonal-entry equation):
//!    `forall (n k : Nat) (z : Zonotope n k) (i : Fin n),
//!       generators_after_ln n k z i i = Fin.sum k (fun j => Rat.abs (z.generators i j))`.
//!    The diagonal entry IS the per-row L1 radius. This is genuinely
//!    `k`-consuming (the RHS is `Fin.sum k ...`); it is NOT a count
//!    tautology and would FAIL to type-check against a `k`-discarding
//!    carrier. Proof: `Decidable.rec` on `instDecidableEqFin n i i` — the
//!    `isTrue` branch is `Eq.refl (radius i)`; the `isFalse` branch
//!    refutes `i = i` via `False.elim (h (Eq.refl i))`.
//! 2. **`zonotope_generators_offdiagonal`** (off-diagonal is zero):
//!    `forall (n k : Nat) (z : Zonotope n k) (i i' : Fin n),
//!       i <> i' -> generators_after_ln n k z i i' = Rat.zero`.
//!    Together with (1) this pins the matrix as exactly the diagonal box.
//!    Proof: `Decidable.rec` on `instDecidableEqFin n i i'` — the `isFalse`
//!    branch is `Eq.refl Rat.zero`; the `isTrue` branch contradicts the
//!    `i <> i'` hypothesis via `False.elim (hne h)`.
//!
//! Both proofs are `Declaration::Theorem`s whose transitive axiom closure
//! is `subseteq {propext, Quot.sound, Classical.choice}` (the carrier
//! reuses `Fin.sum`, `Rat.abs`, `instDecidableEqFin`, all axiom-free
//! constructive definitions over the faithful `Fin`/`Rat`-quotient
//! carriers). NO `sorry`, NO `add_decl_structural`, NO `native_decide`.
//!
//! Mirrors the faithful-carrier technique of
//! `nn_verify_zonotope_to_ibp_faithful` (the `radius` row sum) and
//! `nn_verify_zonotope_compress_define` (the `Decidable.rec` index split),
//! and the diagonal `identity_matrix` Kronecker delta in
//! `nn_verify_matrix_rank_defs`.
//!
//! Part of #3590 (Branch B).

use super::nn_verify_zonotope::ZonotopeConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached constants used by the faithful T22 carrier + its two proofs.
struct T22Consts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    rat_zero: Expr,
    rat_abs: Expr,
    fin_sum: Expr,
    eq: Expr,
    eq_refl: Expr,
    false_: Expr,
    false_elim: Expr,
    nn_mat: Expr,
    inst_dec_eq_fin: Expr,
    /// `Decidable.rec.{1}` (motive lands in `Type 0 = Sort 1`).
    dec_rec: Expr,
    /// `Decidable.rec.{0}` (motive lands in `Prop = Sort 0`) — used by the
    /// dependent proof motive whose target is an `Eq` proposition.
    dec_rec_prop: Expr,
    decidable: Expr,
}

impl T22Consts {
    fn new() -> Self {
        let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: c("Nat"),
            rat: c("Rat"),
            fin: c("Fin"),
            rat_zero: c("Rat.zero"),
            rat_abs: c("Rat.abs"),
            fin_sum: c("Fin.sum"),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            eq_refl: Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            false_: c("False"),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            nn_mat: c("NNVerify.NNMat"),
            inst_dec_eq_fin: c("instDecidableEqFin"),
            dec_rec: Expr::const_(
                Name::from_string("Decidable.rec"),
                vec![Level::succ(Level::zero())],
            ),
            dec_rec_prop: Expr::const_(Name::from_string("Decidable.rec"), vec![Level::zero()]),
            decidable: c("Decidable"),
        }
    }

    /// `@Fin n`.
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    /// `@NNVerify.NNMat n n` (the `n x n` generator-matrix type).
    fn mat_nn(&self, n: &Expr) -> Expr {
        Expr::apps(self.nn_mat.clone(), [n.clone(), n.clone()])
    }

    /// `@Eq.{1} (Fin n) a b : Prop`.
    fn fin_eq(&self, fin_n: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.eq.clone(), [fin_n.clone(), a.clone(), b.clone()])
    }

    /// `@Eq.{1} Rat lhs rhs : Prop`.
    fn rat_eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(self.eq.clone(), [self.rat.clone(), lhs, rhs])
    }

    /// `radius i := Fin.sum k (fun (j : Fin k) => Rat.abs (gens_i j))`.
    /// GENUINELY consumes every one of the `k` input generator columns.
    fn radius(&self, parent: &EnvDeclBuilder, fin_k: &Expr, k: &Expr, gens_i: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = ch.fresh_local(fin_k.clone());
        let abs_gij = Expr::app(self.rat_abs.clone(), Expr::app(gens_i.clone(), j));
        let summand = ch.finish_child(ch.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), abs_gij));
        Expr::apps(self.fin_sum.clone(), [k.clone(), summand])
    }

    /// `@instDecidableEqFin n a b : Decidable (Eq (Fin n) a b)`.
    fn dec_inst(&self, n: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.inst_dec_eq_fin.clone(),
            [n.clone(), a.clone(), b.clone()],
        )
    }

    /// The `isTrue`/`isFalse` minor-premise bodies of the carrier's
    /// `Decidable.rec`, parametric in the diagonal index pair. The motive
    /// is `fun (_ : Decidable (i = i')) => Rat`. `radius` is reused on the
    /// diagonal so the entry GENUINELY depends on the `k` input columns.
    ///
    /// Returns `(p, motive, minor_false, minor_true)`.
    #[allow(clippy::type_complexity)]
    fn carrier_branches(
        &self,
        parent: &EnvDeclBuilder,
        fin_n: &Expr,
        fin_k: &Expr,
        k: &Expr,
        gens_i: &Expr,
        i: &Expr,
        ip: &Expr,
    ) -> (Expr, Expr, Expr, Expr) {
        // p : Prop := Eq (Fin n) i i'.
        let p = self.fin_eq(fin_n, i, ip);

        // motive : Decidable p -> Type := fun _ => Rat.
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let dec_p = Expr::app(self.decidable.clone(), p.clone());
            let (d_id, _d) = mb.fresh_local(dec_p.clone());
            mb.finish_child(mb.mk_lam(d_id, BinderInfo::Default, dec_p, self.rat.clone()))
        };

        // isFalse minor : (p -> False) -> Rat := fun _ => Rat.zero  (off-diagonal).
        let minor_false = {
            let not_p = {
                let mut nb = EnvDeclBuilder::child_of(parent);
                let (x_id, _x) = nb.fresh_local(p.clone());
                nb.finish_child(nb.mk_pi(x_id, BinderInfo::Default, p.clone(), self.false_.clone()))
            };
            let mut fb = EnvDeclBuilder::child_of(parent);
            let (hf_id, _hf) = fb.fresh_local(not_p.clone());
            fb.finish_child(fb.mk_lam(hf_id, BinderInfo::Default, not_p, self.rat_zero.clone()))
        };

        // isTrue minor : p -> Rat := fun _ => radius_i  (diagonal: per-row L1 radius).
        let minor_true = {
            let mut tb = EnvDeclBuilder::child_of(parent);
            let (ht_id, _ht) = tb.fresh_local(p.clone());
            let radius = self.radius(&tb, fin_k, k, gens_i);
            tb.finish_child(tb.mk_lam(ht_id, BinderInfo::Default, p.clone(), radius))
        };

        (p, motive, minor_false, minor_true)
    }
}

impl Environment {
    /// T22: `NNVerify.LayerNorm.zonotope_generators_reset`
    ///
    /// FAITHFUL MATRIX RESTATEMENT (Branch B). LayerNorm destroys zonotope
    /// correlation structure and projects onto the axis-aligned box, whose
    /// generator matrix is the `n x n` diagonal radius matrix
    /// `generators_after_ln n k z`. This theorem pins the DIAGONAL ENTRY:
    ///
    /// ```text
    /// forall (n k : Nat) (z : Zonotope n k) (i : Fin n),
    ///   generators_after_ln n k z i i = Fin.sum k (fun j => Rat.abs (z.generators i j))
    /// ```
    ///
    /// i.e. the diagonal entry is the per-row L1 radius — the SAME quantity
    /// the faithful `to_ibp` computes. It is genuinely `k`-consuming (the
    /// RHS is `Fin.sum k ...`), so it is NOT a count tautology and replaces
    /// the retired `generators_after_ln n k = n` masquerade axiom.
    ///
    /// Proof: `@Decidable.rec.{0}` on `instDecidableEqFin n i i` with the
    /// dependent motive `fun d => (Decidable.rec _ (fun _ => Rat) mf mt d) = radius i`.
    /// The `isTrue` branch iota-reduces the carrier to `radius i`, closed by
    /// `Eq.refl Rat (radius i)`; the `isFalse` branch refutes `i = i` via
    /// `False.elim (h (Eq.refl (Fin n) i))`.
    ///
    /// Part of #3590 (Branch B).
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_t22_layernorm_generators_reset_ext(&mut self) -> Result<(), EnvError> {
        // First register the faithful generators_after_ln matrix carrier.
        self.register_generators_after_ln_ext()?;
        self.register_t22_generators_reset_diagonal()?;
        self.register_t22_generators_offdiagonal()
    }

    /// `NNVerify.LayerNorm.generators_after_ln`
    /// `: (n k : Nat) -> Zonotope n k -> NNMat n n`
    ///
    /// FAITHFUL diagonal radius-box generator matrix (reducible
    /// `Declaration::Definition`). For each output row `i` the matrix is
    /// `diag(radius_i)`:
    /// ```text
    /// fun (i i' : Fin n) =>
    ///   @Decidable.rec (Eq (Fin n) i i') (fun _ => Rat)
    ///     (isFalse := fun _ => Rat.zero)     -- off-diagonal
    ///     (isTrue  := fun _ => radius_i)      -- diagonal = Σ_j |G_ij|
    ///     (instDecidableEqFin n i i')
    /// ```
    /// The diagonal entry `radius_i = Fin.sum k (fun j => Rat.abs (z.generators i j))`
    /// GENUINELY consumes all `k` input generator columns, so the carrier is
    /// NOT argument-discarding (M2 is closed structurally). It is registered
    /// reducible so the two T22 proofs can δ-unfold it to reach the
    /// `Decidable.rec` form their motives match against.
    ///
    /// ### History
    ///
    /// - #3495: `Nat -> Nat -> Nat`, body `fun n _ => n` then a cosmetic
    ///   `Nat.rec` wrapper — argument-discarding MASQUERADE (M2+M3).
    /// - #3590 Branch A: co-demoted to `Declaration::Opaque` (same body) to
    ///   block alias collapse; still a `k`-discarding `Nat -> Nat -> Nat`.
    /// - Branch B (this change): replaced with the faithful
    ///   `Zonotope n k -> NNMat n n` diagonal radius matrix that consumes
    ///   `k`. A `Definition` is a computation, not a claim, so it is not in
    ///   the admitted-axiom census.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_generators_after_ln_ext(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.LayerNorm.generators_after_ln");
        // Replace a legacy Opaque/Axiom carrier; only short-circuit when the
        // faithful reducible Definition is already in place.
        if self
            .get_const(&name)
            .is_some_and(|ci| ci.kind == crate::env::types::ConstantKind::Definition)
        {
            return Ok(());
        }
        let c = T22Consts::new();
        let zc = ZonotopeConsts::new();
        let zono_name = Name::from_string("NNVerify.Zonotope");

        // type : (n k : Nat) -> Zonotope n k -> NNMat n n.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let zono_nk = zc.zono_of(n.clone(), k.clone());
            let (z_id, _z) = b.fresh_local(zono_nk.clone());
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, c.mat_nn(&n));
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // value : fun (n k : Nat) (z : Zonotope n k) (i i' : Fin n) => <diag split>.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let zono_nk = zc.zono_of(n.clone(), k.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let fin_n = c.fin_of(&n);
            let fin_k = c.fin_of(&k);
            let gens = Expr::proj(zono_name.clone(), 1, z);

            let row = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ib.fresh_local(fin_n.clone());
                let gens_i = Expr::app(gens.clone(), i.clone());

                let inner = {
                    let mut jb = EnvDeclBuilder::child_of(&ib);
                    let (ip_id, ip) = jb.fresh_local(fin_n.clone());
                    let (p, motive, minor_false, minor_true) =
                        c.carrier_branches(&jb, &fin_n, &fin_k, &k, &gens_i, &i, &ip);
                    let discriminant = c.dec_inst(&n, &i, &ip);
                    let rec_app = Expr::apps(
                        c.dec_rec.clone(),
                        [p, motive, minor_false, minor_true, discriminant],
                    );
                    jb.finish_child(jb.mk_lam(ip_id, BinderInfo::Default, fin_n.clone(), rec_app))
                };
                ib.finish_child(ib.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), inner))
            };

            let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, row);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNVerify.LayerNorm.zonotope_generators_reset` — the diagonal-entry
    /// equation `generators_after_ln n k z i i = radius_i`. See the
    /// module/method docs above for the full statement and proof sketch.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_t22_generators_reset_diagonal(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.LayerNorm.zonotope_generators_reset");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = T22Consts::new();
        let zc = ZonotopeConsts::new();
        let zono_name = Name::from_string("NNVerify.Zonotope");
        let gen_after_ln = Expr::const_(
            Name::from_string("NNVerify.LayerNorm.generators_after_ln"),
            vec![],
        );

        // type : forall (n k) (z : Zonotope n k) (i : Fin n),
        //          generators_after_ln n k z i i = radius_i.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let zono_nk = zc.zono_of(n.clone(), k.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let fin_n = c.fin_of(&n);
            let fin_k = c.fin_of(&k);
            let (i_id, i) = b.fresh_local(fin_n.clone());
            let gens_i = Expr::app(Expr::proj(zono_name.clone(), 1, z.clone()), i.clone());
            let lhs = Expr::apps(
                gen_after_ln.clone(),
                [n.clone(), k.clone(), z.clone(), i.clone(), i.clone()],
            );
            let rhs = c.radius(&b, &fin_k, &k, &gens_i);
            let concl = c.rat_eq(lhs, rhs);
            let r = b.mk_pi(i_id, BinderInfo::Default, fin_n, concl);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // value : fun (n k) (z) (i) => Decidable.rec ... (instDecidableEqFin n i i).
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let zono_nk = zc.zono_of(n.clone(), k.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let fin_n = c.fin_of(&n);
            let fin_k = c.fin_of(&k);
            let (i_id, i) = b.fresh_local(fin_n.clone());
            let gens_i = Expr::app(Expr::proj(zono_name.clone(), 1, z.clone()), i.clone());

            // Carrier branches specialised to the diagonal (i' := i).
            let (p, _carrier_motive, minor_false, minor_true) =
                c.carrier_branches(&b, &fin_n, &fin_k, &k, &gens_i, &i, &i);
            let radius = c.radius(&b, &fin_k, &k, &gens_i);

            // Dependent motive : fun (d : Decidable p) =>
            //   Eq Rat (Decidable.rec p (fun _ => Rat) mf mt d) radius.
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let dec_p = Expr::app(c.decidable.clone(), p.clone());
                let (d_id, d) = mb.fresh_local(dec_p.clone());
                let rat_motive = {
                    let mut rm = EnvDeclBuilder::child_of(&mb);
                    let (e_id, _e) = rm.fresh_local(dec_p.clone());
                    rm.finish_child(rm.mk_lam(
                        e_id,
                        BinderInfo::Default,
                        dec_p.clone(),
                        c.rat.clone(),
                    ))
                };
                let carrier_at_d = Expr::apps(
                    c.dec_rec.clone(),
                    [
                        p.clone(),
                        rat_motive,
                        minor_false.clone(),
                        minor_true.clone(),
                        d,
                    ],
                );
                let eq_body = c.rat_eq(carrier_at_d, radius.clone());
                mb.finish_child(mb.mk_lam(d_id, BinderInfo::Default, dec_p, eq_body))
            };

            // isFalse case : (h : i = i -> False) -> motive (isFalse h).
            //   reduces to Eq Rat Rat.zero radius; refute via False.elim (h (Eq.refl i)).
            let case_false = {
                let not_p = {
                    let mut nb = EnvDeclBuilder::child_of(&b);
                    let (x_id, _x) = nb.fresh_local(p.clone());
                    nb.finish_child(nb.mk_pi(
                        x_id,
                        BinderInfo::Default,
                        p.clone(),
                        c.false_.clone(),
                    ))
                };
                let mut fb = EnvDeclBuilder::child_of(&b);
                let (hf_id, hf) = fb.fresh_local(not_p.clone());
                // goal = Eq Rat Rat.zero radius (motive (isFalse hf), after iota).
                let goal = c.rat_eq(c.rat_zero.clone(), radius.clone());
                let refl_ii = Expr::apps(c.eq_refl.clone(), [fin_n.clone(), i.clone()]);
                let contra = Expr::app(hf.clone(), refl_ii);
                let body = Expr::apps(c.false_elim.clone(), [goal, contra]);
                fb.finish_child(fb.mk_lam(hf_id, BinderInfo::Default, not_p, body))
            };

            // isTrue case : (h : i = i) -> motive (isTrue h).
            //   reduces to Eq Rat radius radius; closed by Eq.refl Rat radius.
            let case_true = {
                let mut tb = EnvDeclBuilder::child_of(&b);
                let (ht_id, _ht) = tb.fresh_local(p.clone());
                let refl_radius = Expr::apps(c.eq_refl.clone(), [c.rat.clone(), radius.clone()]);
                tb.finish_child(tb.mk_lam(ht_id, BinderInfo::Default, p.clone(), refl_radius))
            };

            let discriminant = c.dec_inst(&n, &i, &i);
            let rec_app = Expr::apps(
                c.dec_rec_prop.clone(),
                [p, motive, case_false, case_true, discriminant],
            );

            let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, rec_app);
            let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.LayerNorm.zonotope_generators_offdiagonal` — the
    /// companion off-diagonal-is-zero theorem:
    /// ```text
    /// forall (n k : Nat) (z : Zonotope n k) (i i' : Fin n),
    ///   i <> i' -> generators_after_ln n k z i i' = Rat.zero
    /// ```
    /// Together with the diagonal equation this characterises the LayerNorm
    /// generator matrix as exactly `diag(radius_i)`. Proof: `Decidable.rec`
    /// on `instDecidableEqFin n i i'` — `isFalse` is `Eq.refl Rat.zero`;
    /// `isTrue (h : i = i')` contradicts the hypothesis via
    /// `False.elim (hne h)`.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_t22_generators_offdiagonal(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.LayerNorm.zonotope_generators_offdiagonal");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = T22Consts::new();
        let zc = ZonotopeConsts::new();
        let zono_name = Name::from_string("NNVerify.Zonotope");
        let gen_after_ln = Expr::const_(
            Name::from_string("NNVerify.LayerNorm.generators_after_ln"),
            vec![],
        );

        // type : forall (n k) (z) (i i' : Fin n), (i = i' -> False) ->
        //          generators_after_ln n k z i i' = Rat.zero.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let zono_nk = zc.zono_of(n.clone(), k.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let fin_n = c.fin_of(&n);
            let (i_id, i) = b.fresh_local(fin_n.clone());
            let (ip_id, ip) = b.fresh_local(fin_n.clone());
            let ne_ty = {
                let mut nb = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = nb.fresh_local(c.fin_eq(&fin_n, &i, &ip));
                nb.finish_child(nb.mk_pi(
                    x_id,
                    BinderInfo::Default,
                    c.fin_eq(&fin_n, &i, &ip),
                    c.false_.clone(),
                ))
            };
            let (hne_id, _hne) = b.fresh_local(ne_ty.clone());
            let lhs = Expr::apps(
                gen_after_ln.clone(),
                [n.clone(), k.clone(), z.clone(), i.clone(), ip.clone()],
            );
            let concl = c.rat_eq(lhs, c.rat_zero.clone());
            let r = b.mk_pi(hne_id, BinderInfo::Default, ne_ty, concl);
            let r = b.mk_pi(ip_id, BinderInfo::Default, fin_n.clone(), r);
            let r = b.mk_pi(i_id, BinderInfo::Default, fin_n, r);
            let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
            let r = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let zono_nk = zc.zono_of(n.clone(), k.clone());
            let (z_id, z) = b.fresh_local(zono_nk.clone());
            let fin_n = c.fin_of(&n);
            let fin_k = c.fin_of(&k);
            let (i_id, i) = b.fresh_local(fin_n.clone());
            let (ip_id, ip) = b.fresh_local(fin_n.clone());
            let gens_i = Expr::app(Expr::proj(zono_name.clone(), 1, z.clone()), i.clone());

            let (p, _carrier_motive, minor_false, minor_true) =
                c.carrier_branches(&b, &fin_n, &fin_k, &k, &gens_i, &i, &ip);

            let ne_ty = {
                let mut nb = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = nb.fresh_local(p.clone());
                nb.finish_child(nb.mk_pi(x_id, BinderInfo::Default, p.clone(), c.false_.clone()))
            };
            let (hne_id, hne) = b.fresh_local(ne_ty.clone());

            // Dependent motive : fun (d : Decidable p) =>
            //   Eq Rat (Decidable.rec p (fun _ => Rat) mf mt d) Rat.zero.
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let dec_p = Expr::app(c.decidable.clone(), p.clone());
                let (d_id, d) = mb.fresh_local(dec_p.clone());
                let rat_motive = {
                    let mut rm = EnvDeclBuilder::child_of(&mb);
                    let (e_id, _e) = rm.fresh_local(dec_p.clone());
                    rm.finish_child(rm.mk_lam(
                        e_id,
                        BinderInfo::Default,
                        dec_p.clone(),
                        c.rat.clone(),
                    ))
                };
                let carrier_at_d = Expr::apps(
                    c.dec_rec.clone(),
                    [
                        p.clone(),
                        rat_motive,
                        minor_false.clone(),
                        minor_true.clone(),
                        d,
                    ],
                );
                let eq_body = c.rat_eq(carrier_at_d, c.rat_zero.clone());
                mb.finish_child(mb.mk_lam(d_id, BinderInfo::Default, dec_p, eq_body))
            };

            // isFalse case : (h : i = i' -> False) -> motive (isFalse h).
            //   reduces to Eq Rat Rat.zero Rat.zero; Eq.refl Rat Rat.zero.
            let case_false = {
                let mut fb = EnvDeclBuilder::child_of(&b);
                let (hf_id, _hf) = fb.fresh_local(ne_ty.clone());
                let refl_zero = Expr::apps(c.eq_refl.clone(), [c.rat.clone(), c.rat_zero.clone()]);
                fb.finish_child(fb.mk_lam(hf_id, BinderInfo::Default, ne_ty.clone(), refl_zero))
            };

            // isTrue case : (h : i = i') -> motive (isTrue h).
            //   contradicts hne; goal via False.elim (Eq Rat radius_i Rat.zero) (hne h).
            let case_true = {
                let mut tb = EnvDeclBuilder::child_of(&b);
                let (ht_id, ht) = tb.fresh_local(p.clone());
                // goal after iota = Eq Rat radius_i Rat.zero (mt h = radius_i).
                let radius = c.radius(&tb, &fin_k, &k, &gens_i);
                let goal = c.rat_eq(radius, c.rat_zero.clone());
                let contra = Expr::app(hne.clone(), ht);
                let body = Expr::apps(c.false_elim.clone(), [goal, contra]);
                tb.finish_child(tb.mk_lam(ht_id, BinderInfo::Default, p.clone(), body))
            };

            let discriminant = c.dec_inst(&n, &i, &ip);
            let rec_app = Expr::apps(
                c.dec_rec_prop.clone(),
                [p, motive, case_false, case_true, discriminant],
            );

            let e = b.mk_lam(hne_id, BinderInfo::Default, ne_ty, rec_app);
            let e = b.mk_lam(ip_id, BinderInfo::Default, fin_n.clone(), e);
            let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, e);
            let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

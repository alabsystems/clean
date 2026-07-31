// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Term builders for the general n-row constructive Farkas combination.
//!
//! Split out of `nn_verify_farkas_list.rs` to keep that module under the
//! 500-line limit, mirroring the
//! `nn_verify_foundation_theorems_farkas_constructive` /
//! `..._constructive_proofs` split. Hosts the shared `FarkasListConsts`
//! term builders, the `List.rec` fold definitions
//! (`farkasLower`/`farkasUpper`/`farkasRowsValid`), and the
//! `farkas_combine_list` proof term.
//!
//! See `nn_verify_farkas_list.rs` for the encoding, theorem statement, and
//! proof-strategy documentation.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::nn_verify_foundation_theorems_farkas_constructive_proofs::FarkasConsts;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the list-folded Farkas combination.
pub(super) struct FarkasListConsts {
    fk: FarkasConsts,
    rat: Expr,
    rat_zero: Expr,
    prod: Expr,           // Prod @{0,0}
    prod_fst: Expr,       // Prod.fst @{0,0}
    prod_snd: Expr,       // Prod.snd @{0,0}
    list: Expr,           // List @{0}
    list_rec_type0: Expr, // List.rec @{1,0}: motive → Type 0 (Rat-valued folds)
    list_rec_prop: Expr,  // List.rec @{0,0}: motive → Prop (validity fold + proof)
    and: Expr,
    and_left: Expr,
    and_right: Expr,
    true_: Expr,
    le_refl: Expr,
    prop: Expr,
}

impl FarkasListConsts {
    pub(super) fn new() -> Self {
        let lvl0 = Level::zero();
        let lvl1 = Level::succ(Level::zero());
        Self {
            fk: FarkasConsts::new(),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            prod: Expr::const_(Name::from_string("Prod"), vec![lvl0.clone(), lvl0.clone()]),
            prod_fst: Expr::const_(
                Name::from_string("Prod.fst"),
                vec![lvl0.clone(), lvl0.clone()],
            ),
            prod_snd: Expr::const_(
                Name::from_string("Prod.snd"),
                vec![lvl0.clone(), lvl0.clone()],
            ),
            list: Expr::const_(Name::from_string("List"), vec![lvl0.clone()]),
            list_rec_type0: Expr::const_(Name::from_string("List.rec"), vec![lvl1, lvl0.clone()]),
            list_rec_prop: Expr::const_(Name::from_string("List.rec"), vec![lvl0.clone(), lvl0]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            and_left: Expr::const_(Name::from_string("And.left"), vec![]),
            and_right: Expr::const_(Name::from_string("And.right"), vec![]),
            true_: Expr::const_(Name::from_string("True"), vec![]),
            le_refl: Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
            prop: Expr::sort(Level::zero()),
        }
    }

    /// `Prod Rat Rat` — the inner `(a, b)` pair type.
    fn pair_ty(&self) -> Expr {
        Expr::app(
            Expr::app(self.prod.clone(), self.rat.clone()),
            self.rat.clone(),
        )
    }

    /// `Row := Prod Rat (Prod Rat Rat)` — the `(mu, a, b)` row type.
    fn row_ty(&self) -> Expr {
        Expr::app(
            Expr::app(self.prod.clone(), self.rat.clone()),
            self.pair_ty(),
        )
    }

    /// `List Row`.
    fn rows_ty(&self) -> Expr {
        Expr::app(self.list.clone(), self.row_ty())
    }

    /// `Prod.fst @Rat @(Prod Rat Rat) row : Rat` — extract `mu`.
    fn mu(&self, row: &Expr) -> Expr {
        Expr::apps(
            self.prod_fst.clone(),
            [self.rat.clone(), self.pair_ty(), row.clone()],
        )
    }

    /// `Prod.snd @Rat @(Prod Rat Rat) row : Prod Rat Rat` — extract `(a, b)`.
    fn ab_pair(&self, row: &Expr) -> Expr {
        Expr::apps(
            self.prod_snd.clone(),
            [self.rat.clone(), self.pair_ty(), row.clone()],
        )
    }

    /// `Prod.fst @Rat @Rat (ab_pair row) : Rat` — extract `a`.
    fn a(&self, row: &Expr) -> Expr {
        Expr::apps(
            self.prod_fst.clone(),
            [self.rat.clone(), self.rat.clone(), self.ab_pair(row)],
        )
    }

    /// `Prod.snd @Rat @Rat (ab_pair row) : Rat` — extract `b`.
    fn b(&self, row: &Expr) -> Expr {
        Expr::apps(
            self.prod_snd.clone(),
            [self.rat.clone(), self.rat.clone(), self.ab_pair(row)],
        )
    }

    /// `And a b`.
    fn and_(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.and.clone(), a), b)
    }

    /// `And.left @a @b h`.
    fn and_left_app(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_left.clone(), [a, b, h])
    }

    /// `And.right @a @b h`.
    fn and_right_app(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.and_right.clone(), [a, b, h])
    }

    /// `farkasLower rows` as a const application.
    fn lower_app(&self, rows: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("NNVerify.farkasLower"), vec![]),
            rows.clone(),
        )
    }

    /// `farkasUpper rows` as a const application.
    fn upper_app(&self, rows: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("NNVerify.farkasUpper"), vec![]),
            rows.clone(),
        )
    }

    /// `farkasRowsValid rows` as a const application.
    fn valid_app(&self, rows: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("NNVerify.farkasRowsValid"), vec![]),
            rows.clone(),
        )
    }

    /// Per-row validity proposition `And (0 ≤ mu) (a ≤ b)`.
    fn row_valid_prop(&self, row: &Expr) -> Expr {
        self.and_(
            self.fk.rat_le(self.rat_zero.clone(), self.mu(row)),
            self.fk.rat_le(self.a(row), self.b(row)),
        )
    }

    // -- Public-in-`env` builders used by the certificate parser to construct
    //    a concrete `List Row` and the applied `farkas_combine_list` instance.

    /// `Row := Prod Rat (Prod Rat Rat)` type — exposed for the parser.
    #[cfg(test)]
    pub(in crate::env) fn row_type(&self) -> Expr {
        self.row_ty()
    }

    /// `List Row` type — exposed for the parser.
    #[cfg(test)]
    pub(in crate::env) fn rows_type(&self) -> Expr {
        self.rows_ty()
    }

    /// Build a concrete row literal `Prod.mk Rat (Prod Rat Rat) mu
    /// (Prod.mk Rat Rat a b) : Row` from the three rational `Expr`s.
    #[cfg(test)]
    pub(in crate::env) fn mk_row_lit(&self, mu: Expr, a: Expr, b: Expr) -> Expr {
        let prod_mk = Expr::const_(
            Name::from_string("Prod.mk"),
            vec![Level::zero(), Level::zero()],
        );
        let inner = Expr::apps(prod_mk.clone(), [self.rat.clone(), self.rat.clone(), a, b]);
        Expr::apps(prod_mk, [self.rat.clone(), self.pair_ty(), mu, inner])
    }

    /// Fold a slice of `Row` literals into `r0 :: r1 :: … :: List.nil Row`.
    #[cfg(test)]
    pub(in crate::env) fn mk_rows_list(&self, rows: &[Expr]) -> Expr {
        let row_ty = self.row_ty();
        let nil = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            row_ty.clone(),
        );
        let cons = Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]);
        rows.iter().rev().fold(nil, |acc, row| {
            Expr::apps(cons.clone(), [row_ty.clone(), row.clone(), acc])
        })
    }

    /// `farkasRowsValid rows` proposition — exposed for the parser hypothesis.
    #[cfg(test)]
    pub(in crate::env) fn rows_valid_prop(&self, rows: &Expr) -> Expr {
        self.valid_app(rows)
    }

    /// `farkasLower rows ≤ farkasUpper rows` proposition — the combination
    /// conclusion the parser registers, exposed for the parser.
    #[cfg(test)]
    pub(in crate::env) fn combine_concl(&self, rows: &Expr) -> Expr {
        self.fk.rat_le(self.lower_app(rows), self.upper_app(rows))
    }

    /// `@NNVerify.farkas_combine_list rows hv : farkasLower rows ≤
    /// farkasUpper rows` — the kernel-checked applied combination theorem.
    #[cfg(test)]
    pub(in crate::env) fn apply_combine_list(&self, rows: &Expr, hv: &Expr) -> Expr {
        let thm = Expr::const_(Name::from_string("NNVerify.farkas_combine_list"), vec![]);
        Expr::apps(thm, [rows.clone(), hv.clone()])
    }
}

/// Construct the parser-facing builder. Public-in-`env` factory so the cert
/// parser can build `List Row` instances without re-deriving the encoding.
#[cfg(test)]
pub(in crate::env) fn farkas_list_consts() -> FarkasListConsts {
    FarkasListConsts::new()
}

// ── farkasLower / farkasUpper : List Row → Rat ─────────────────────────

/// Type of `farkasLower` / `farkasUpper`: `List Row → Rat`.
pub(super) fn build_fold_type(c: &FarkasListConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rows_id, _rows) = b.fresh_local(c.rows_ty());
    let e = b.mk_pi(rows_id, BinderInfo::Default, c.rows_ty(), c.rat.clone());
    b.finish(e)
}

/// Value of a `Rat`-valued foldr over rows: `fun rows => List.rec @{1,0}
/// @Row (fun _ => Rat) Rat.zero (fun row _tail ih => mu*comp + ih) rows`,
/// where `comp` selects `a` (lower) or `b` (upper).
pub(super) fn build_fold_value(c: &FarkasListConsts, upper: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rows_id, rows) = b.fresh_local(c.rows_ty());

    // Motive: fun (_ : List Row) => Rat.  Rat : Type 0, so u_1 = 1.
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (m_id, _m) = ch.fresh_local(c.rows_ty());
        let r = ch.mk_lam(m_id, BinderInfo::Default, c.rows_ty(), c.rat.clone());
        ch.finish_child(r)
    };

    // Nil case: Rat.zero : motive [] = Rat.
    let nil_case = c.rat_zero.clone();

    // Cons case: fun (row : Row) (_tail : List Row) (ih : Rat) =>
    //              Rat.add (Rat.mul mu comp) ih
    let cons_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (row_id, row) = ch.fresh_local(c.row_ty());
        let (tail_id, _tail) = ch.fresh_local(c.rows_ty());
        let (ih_id, ih) = ch.fresh_local(c.rat.clone());
        let comp = if upper { c.b(&row) } else { c.a(&row) };
        let term = c.fk.mul(c.mu(&row), comp);
        let body = c.fk.add(term, ih);
        let r = ch.mk_lam(ih_id, BinderInfo::Default, c.rat.clone(), body);
        let r = ch.mk_lam(tail_id, BinderInfo::Default, c.rows_ty(), r);
        let r = ch.mk_lam(row_id, BinderInfo::Default, c.row_ty(), r);
        ch.finish_child(r)
    };

    let body = Expr::apps(
        c.list_rec_type0.clone(),
        [c.row_ty(), motive, nil_case, cons_case, rows],
    );
    let e = b.mk_lam(rows_id, BinderInfo::Default, c.rows_ty(), body);
    b.finish(e)
}

// ── farkasRowsValid : List Row → Prop ──────────────────────────────────

/// Type of `farkasRowsValid`: `List Row → Prop`.
pub(super) fn build_valid_type(c: &FarkasListConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rows_id, _rows) = b.fresh_local(c.rows_ty());
    let e = b.mk_pi(rows_id, BinderInfo::Default, c.rows_ty(), c.prop.clone());
    b.finish(e)
}

/// Value: `fun rows => List.rec @{1,0} @Row (fun _ => Prop) True
///   (fun row _tail ih => And (And (0 ≤ mu) (a ≤ b)) ih) rows`.
pub(super) fn build_valid_value(c: &FarkasListConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rows_id, rows) = b.fresh_local(c.rows_ty());

    // Motive: fun (_ : List Row) => Prop.  The *result* of the fold is a
    // proposition-valued *type* (`Prop = Sort 0`), so `motive list = Prop`
    // has type `Type 0 = Sort 1`, requiring u_motive = 1 (`list_rec_type0`).
    // (Contrast the combine_list *proof* below, whose motive result is a
    // proof of a Prop, hence `@{0,0}`.)
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (m_id, _m) = ch.fresh_local(c.rows_ty());
        let r = ch.mk_lam(m_id, BinderInfo::Default, c.rows_ty(), c.prop.clone());
        ch.finish_child(r)
    };

    // Nil case: True : motive [] = Prop.
    let nil_case = c.true_.clone();

    // Cons case: fun (row : Row) (_tail : List Row) (ih : Prop) =>
    //   And (And (0 ≤ mu) (a ≤ b)) ih
    let cons_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (row_id, row) = ch.fresh_local(c.row_ty());
        let (tail_id, _tail) = ch.fresh_local(c.rows_ty());
        let (ih_id, ih) = ch.fresh_local(c.prop.clone());
        let body = c.and_(c.row_valid_prop(&row), ih);
        let r = ch.mk_lam(ih_id, BinderInfo::Default, c.prop.clone(), body);
        let r = ch.mk_lam(tail_id, BinderInfo::Default, c.rows_ty(), r);
        let r = ch.mk_lam(row_id, BinderInfo::Default, c.row_ty(), r);
        ch.finish_child(r)
    };

    let body = Expr::apps(
        c.list_rec_type0.clone(),
        [c.row_ty(), motive, nil_case, cons_case, rows],
    );
    let e = b.mk_lam(rows_id, BinderInfo::Default, c.rows_ty(), body);
    b.finish(e)
}

// ── farkas_combine_list theorem ────────────────────────────────────────

/// Type: `∀ (rows : List Row),
///   farkasRowsValid rows → farkasLower rows ≤ farkasUpper rows`.
pub(super) fn build_combine_list_type(c: &FarkasListConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rows_id, rows) = b.fresh_local(c.rows_ty());
    let valid = c.valid_app(&rows);
    let concl = c.fk.rat_le(c.lower_app(&rows), c.upper_app(&rows));
    let (h_id, _h) = b.fresh_local(valid.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, valid, concl);
    let e = b.mk_pi(rows_id, BinderInfo::Default, c.rows_ty(), e);
    b.finish(e)
}

/// Cons-case proof term, built as a child builder of `parent`.
///
/// Shape (after motive specialization):
/// `fun (row : Row) (tail : List Row)
///      (ih : farkasRowsValid tail → farkasLower tail ≤ farkasUpper tail)
///      (hv : And (And (0≤mu) (a≤b)) (farkasRowsValid tail)) =>
///    add_le_add (mu*a) (mu*b) (farkasLower tail) (farkasUpper tail)
///      (scale mu a b hmu hab)
///      (ih (And.right hv))`
/// which inhabits `mu*a + farkasLower tail ≤ mu*b + farkasUpper tail`,
/// i.e. `farkasLower (row::tail) ≤ farkasUpper (row::tail)`.
fn build_combine_list_cons_case(c: &FarkasListConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(parent);
    let (row_id, row) = ch.fresh_local(c.row_ty());
    let (tail_id, tail) = ch.fresh_local(c.rows_ty());

    // IH type: farkasRowsValid tail → farkasLower tail ≤ farkasUpper tail
    let ih_type = {
        let valid_tail = c.valid_app(&tail);
        let concl_tail = c.fk.rat_le(c.lower_app(&tail), c.upper_app(&tail));
        let (h_id, _) = ch.fresh_local(valid_tail.clone());
        ch.mk_pi(h_id, BinderInfo::Default, valid_tail, concl_tail)
    };
    let (ih_id, ih) = ch.fresh_local(ih_type.clone());

    // Validity hypothesis: And (row_valid_prop row) (farkasRowsValid tail)
    let row_valid = c.row_valid_prop(&row);
    let tail_valid = c.valid_app(&tail);
    let hv_type = c.and_(row_valid.clone(), tail_valid.clone());
    let (hv_id, hv) = ch.fresh_local(hv_type.clone());

    // Decompose hv.
    let h_row = c.and_left_app(row_valid.clone(), tail_valid.clone(), hv.clone());
    let h_tail = c.and_right_app(row_valid.clone(), tail_valid.clone(), hv);

    // Decompose the per-row And: hmu : 0 ≤ mu, hab : a ≤ b.
    let mu = c.mu(&row);
    let a = c.a(&row);
    let bb = c.b(&row);
    let hmu_prop = c.fk.rat_le(c.rat_zero.clone(), mu.clone());
    let hab_prop = c.fk.rat_le(a.clone(), bb.clone());
    let hmu = c.and_left_app(hmu_prop.clone(), hab_prop.clone(), h_row.clone());
    let hab = c.and_right_app(hmu_prop, hab_prop, h_row);

    // Head bound: mu*a ≤ mu*b.
    let head_bound = c.fk.scale(mu.clone(), a.clone(), bb.clone(), hmu, hab);
    // Tail bound: farkasLower tail ≤ farkasUpper tail, via IH.
    let tail_bound = Expr::app(ih, h_tail);

    // Combine: add_le_add (mu*a) (mu*b) (lower tail) (upper tail) head tail.
    let mu_a = c.fk.mul(mu.clone(), a);
    let mu_b = c.fk.mul(mu, bb);
    let lo_tail = c.lower_app(&tail);
    let up_tail = c.upper_app(&tail);
    let proof =
        c.fk.add_le(mu_a, mu_b, lo_tail, up_tail, head_bound, tail_bound);

    let r = ch.mk_lam(hv_id, BinderInfo::Default, hv_type, proof);
    let r = ch.mk_lam(ih_id, BinderInfo::Default, ih_type, r);
    let r = ch.mk_lam(tail_id, BinderInfo::Default, c.rows_ty(), r);
    let r = ch.mk_lam(row_id, BinderInfo::Default, c.row_ty(), r);
    ch.finish_child(r)
}

/// Proof via `List.rec @{0,0}` with motive
/// `fun rows => farkasRowsValid rows → farkasLower rows ≤ farkasUpper rows`.
pub(super) fn build_combine_list_proof(c: &FarkasListConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rows_id, rows) = b.fresh_local(c.rows_ty());

    // Motive: fun rows => farkasRowsValid rows → farkasLower rows ≤ farkasUpper rows.
    // Result is a Prop (function into Prop is Prop), so u_motive = 0.
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (m_id, m_rows) = ch.fresh_local(c.rows_ty());
        let valid = c.valid_app(&m_rows);
        let concl = c.fk.rat_le(c.lower_app(&m_rows), c.upper_app(&m_rows));
        let (h_id, _) = ch.fresh_local(valid.clone());
        let inner = ch.mk_pi(h_id, BinderInfo::Default, valid, concl);
        let r = ch.mk_lam(m_id, BinderInfo::Default, c.rows_ty(), inner);
        ch.finish_child(r)
    };

    // Nil case: fun (_hv : farkasRowsValid []) => Rat.le_refl Rat.zero.
    // farkasLower [] ≡ Rat.zero and farkasUpper [] ≡ Rat.zero by iota
    // reduction, so the goal 0 ≤ 0 is met by reflexivity.
    let nil_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let nil_valid = {
            // farkasRowsValid [] reduces to True; but we state the hypothesis
            // at the motive-applied type which the kernel will reduce.
            c.valid_app(&Expr::app(
                Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
                c.row_ty(),
            ))
        };
        let (h_id, _) = ch.fresh_local(nil_valid.clone());
        let refl = Expr::app(c.le_refl.clone(), c.rat_zero.clone());
        let r = ch.mk_lam(h_id, BinderInfo::Default, nil_valid, refl);
        ch.finish_child(r)
    };

    let cons_case = build_combine_list_cons_case(c, &b);

    let body = Expr::apps(
        c.list_rec_prop.clone(),
        [c.row_ty(), motive, nil_case, cons_case, rows],
    );
    let e = b.mk_lam(rows_id, BinderInfo::Default, c.rows_ty(), body);
    b.finish(e)
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.DeRham namespace (#1444).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.DeRham";
pub(crate) const DECL_COUNT: usize = 27;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.DeRham.SmoothManifold",
    "Topology.DeRham.DifferentialForm",
    "Topology.DeRham.exterior_derivative",
    "Topology.DeRham.d_squared_zero",
    "Topology.DeRham.wedge_anticommutative",
    "Topology.DeRham.leibniz_rule",
    "Topology.DeRham.exact_is_closed",
    "Topology.DeRham.stokes_theorem",
    "Topology.DeRham.hodge_involution",
    "Topology.DeRham.hodge_decomposition",
    "Topology.DeRham.wedge",
    "Topology.DeRham.ClosedForm",
    "Topology.DeRham.ExactForm",
    "Topology.DeRham.HarmonicForm",
    "Topology.DeRham.H",
    "Topology.DeRham.H_is_add_comm_group",
    "Topology.DeRham.derham_theorem",
    "Topology.DeRham.poincare_lemma",
    "Topology.DeRham.integrate",
    "Topology.DeRham.pullback",
    "Topology.DeRham.pullback_commutes_d",
    "Topology.DeRham.HodgeStar",
    "Topology.DeRham.codifferential",
    "Topology.DeRham.Laplacian",
    "Topology.DeRham.harmonic_rep",
    "Topology.DeRham.betti",
    "Topology.DeRham.mayer_vietoris",
];

struct DeRhamCtx {
    u: Name,
    v: Name,
    u_level: Level,
    v_level: Level,
    type_u: Expr,
    type_v: Expr,
    prop: Expr,
}

impl DeRhamCtx {
    fn new() -> Self {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        Self {
            type_u: Expr::sort(Level::succ(u_level.clone())),
            type_v: Expr::sort(Level::succ(v_level.clone())),
            prop: Expr::sort(Level::zero()),
            u,
            v,
            u_level,
            v_level,
        }
    }

    fn nat_const(&self) -> Expr {
        Expr::const_(Name::from_string("Nat"), vec![])
    }

    fn rat_const(&self) -> Expr {
        Expr::const_(Name::from_string("Rat"), vec![])
    }

    fn topological_space(&self, level: Level) -> Expr {
        Expr::const_(Name::from_string("TopologicalSpace"), vec![level])
    }

    fn differential_form(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.DeRham.DifferentialForm"),
            vec![self.u_level.clone()],
        )
    }

    /// Ω^k(M) = DifferentialForm M ts dim k
    fn mathverse(&self, m: &Expr, ts: &Expr, dim: &Expr, k: &Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(self.differential_form(), m.clone()), ts.clone()),
                dim.clone(),
            ),
            k.clone(),
        )
    }

    fn to_axiom_u(&self, name: &str, type_: Expr) -> ConstantInfo {
        ConstantInfo {
            name: Name::from_string(name),
            level_params: vec![self.u.clone()],
            type_,
            value: None,
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            kind: ConstantKind::Axiom,
        }
    }

    fn to_axiom_uv(&self, name: &str, type_: Expr) -> ConstantInfo {
        ConstantInfo {
            name: Name::from_string(name),
            level_params: vec![self.u.clone(), self.v.clone()],
            type_,
            value: None,
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            kind: ConstantKind::Axiom,
        }
    }

    /// {M : Type u} → [TS M] → <ret>
    fn build_ts_type_u(&self, ret: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), m);
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, ret);
        b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// (k : Nat) → {M : Type u} → [TS M] → (dim : Nat) → <ret>
    fn build_nat_ts_dim_type(&self, ret: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let nat_ty = self.nat_const();
        let (k_id, _) = b.fresh_local(nat_ty.clone());
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), m);
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let (d_id, _) = b.fresh_local(nat_ty.clone());
        let e = b.mk_pi(d_id, BinderInfo::Default, nat_ty.clone(), ret);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let e = b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), e);
        b.mk_pi(k_id, BinderInfo::Default, nat_ty, e)
    }

    /// {M} → [TS M] → {dim} → {k} → (ω : Ω^k(M)) → <ret(m, ts, dim, k)>
    fn build_form_to_ret(&self, ret_fn: impl Fn(&Expr, &Expr, &Expr, &Expr) -> Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), m.clone());
        let (ts_id, ts) = b.fresh_local(ts_ty.clone());
        let nat_ty = self.nat_const();
        let (dim_id, dim) = b.fresh_local(nat_ty.clone());
        let (k_id, k) = b.fresh_local(nat_ty.clone());
        let mathverse_k = self.mathverse(&m, &ts, &dim, &k);
        let (w_id, _) = b.fresh_local(mathverse_k.clone());
        let result = ret_fn(&m, &ts, &dim, &k);
        let e = b.mk_pi(w_id, BinderInfo::Default, mathverse_k, result);
        let e = b.mk_pi(k_id, BinderInfo::Implicit, nat_ty.clone(), e);
        let e = b.mk_pi(dim_id, BinderInfo::Implicit, nat_ty, e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// {M} → [TS M] → {dim} → {k} → Prop
    fn build_ts_dk_prop(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), m);
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let nat_ty = self.nat_const();
        let (dim_id, _) = b.fresh_local(nat_ty.clone());
        let (k_id, _) = b.fresh_local(nat_ty.clone());
        let e = b.mk_pi(
            k_id,
            BinderInfo::Implicit,
            nat_ty.clone(),
            self.prop.clone(),
        );
        let e = b.mk_pi(dim_id, BinderInfo::Implicit, nat_ty, e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// wedge : {M} → [TS M] → {dim} → {j} → {k} → Ω^j → Ω^k → Ω^(j+k)
    fn build_wedge_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), m.clone());
        let (ts_id, ts) = b.fresh_local(ts_ty.clone());
        let nat_ty = self.nat_const();
        let (dim_id, dim) = b.fresh_local(nat_ty.clone());
        let (j_id, j) = b.fresh_local(nat_ty.clone());
        let (k_id, k) = b.fresh_local(nat_ty.clone());
        let mathverse_j = self.mathverse(&m, &ts, &dim, &j);
        let mathverse_k = self.mathverse(&m, &ts, &dim, &k);
        let j_plus_k = Expr::app(
            Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), j),
            k,
        );
        let mathverse_jk = self.mathverse(&m, &ts, &dim, &j_plus_k);
        let (wj_id, _) = b.fresh_local(mathverse_j.clone());
        let (wk_id, _) = b.fresh_local(mathverse_k.clone());
        let e = b.mk_pi(wk_id, BinderInfo::Default, mathverse_k, mathverse_jk);
        let e = b.mk_pi(wj_id, BinderInfo::Default, mathverse_j, e);
        let e = b.mk_pi(k_id, BinderInfo::Implicit, nat_ty.clone(), e);
        let e = b.mk_pi(j_id, BinderInfo::Implicit, nat_ty.clone(), e);
        let e = b.mk_pi(dim_id, BinderInfo::Implicit, nat_ty, e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// H_is_add_comm_group : (k : Nat) → {M : Type u} → [TS M] → (dim : Nat) → AddCommGroup (H k M dim)
    fn build_h_is_add_comm_group_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let nat_ty = self.nat_const();
        let (k_id, k) = b.fresh_local(nat_ty.clone());
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), m.clone());
        let (ts_id, ts) = b.fresh_local(ts_ty.clone());
        let (d_id, d) = b.fresh_local(nat_ty.clone());
        let h_app = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.DeRham.H"),
                            vec![self.u_level.clone()],
                        ),
                        k,
                    ),
                    m,
                ),
                ts,
            ),
            d,
        );
        let ret = Expr::app(
            Expr::const_(
                Name::from_string("AddCommGroup"),
                vec![self.u_level.clone()],
            ),
            h_app,
        );
        let e = b.mk_pi(d_id, BinderInfo::Default, nat_ty.clone(), ret);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let e = b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), e);
        b.mk_pi(k_id, BinderInfo::Default, nat_ty, e)
    }

    /// poincare_lemma : {M : Type u} → [TS M] → Contractible M → (k : Nat) → Prop
    fn build_poincare_lemma_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), m.clone());
        let (ts_id, ts) = b.fresh_local(ts_ty.clone());
        let contr_ty = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Topology.Contractible"),
                    vec![self.u_level.clone()],
                ),
                m,
            ),
            ts,
        );
        let (c_id, _) = b.fresh_local(contr_ty.clone());
        let nat_ty = self.nat_const();
        let (k_id, _) = b.fresh_local(nat_ty.clone());
        let e = b.mk_pi(k_id, BinderInfo::Default, nat_ty, self.prop.clone());
        let e = b.mk_pi(c_id, BinderInfo::Default, contr_ty, e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// pullback : {M : Type u} → {N : Type v} → [TS M] → [TS N] → (f : M → N) →
    ///   {dim} → {k} → Ω^k(N) → Ω^k(M)
    fn build_pullback_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let (n_id, n) = b.fresh_local(self.type_v.clone());
        let ts_m_ty = Expr::app(self.topological_space(self.u_level.clone()), m.clone());
        let (tsm_id, tsm) = b.fresh_local(ts_m_ty.clone());
        let ts_n_ty = Expr::app(self.topological_space(self.v_level.clone()), n.clone());
        let (tsn_id, tsn) = b.fresh_local(ts_n_ty.clone());
        let f_ty = Expr::pi(BinderInfo::Default, m.clone(), n.clone());
        let (f_id, _) = b.fresh_local(f_ty.clone());
        let nat_ty = self.nat_const();
        let (dim_id, dim) = b.fresh_local(nat_ty.clone());
        let (k_id, k) = b.fresh_local(nat_ty.clone());
        let df_v = Expr::const_(
            Name::from_string("Topology.DeRham.DifferentialForm"),
            vec![self.v_level.clone()],
        );
        let mathverse_k_n = Expr::app(
            Expr::app(Expr::app(Expr::app(df_v, n), tsn), dim.clone()),
            k.clone(),
        );
        let mathverse_k_m = self.mathverse(&m, &tsm, &dim, &k);
        let (w_id, _) = b.fresh_local(mathverse_k_n.clone());
        let e = b.mk_pi(w_id, BinderInfo::Default, mathverse_k_n, mathverse_k_m);
        let e = b.mk_pi(k_id, BinderInfo::Implicit, nat_ty.clone(), e);
        let e = b.mk_pi(dim_id, BinderInfo::Implicit, nat_ty, e);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
        let e = b.mk_pi(tsn_id, BinderInfo::InstImplicit, ts_n_ty, e);
        let e = b.mk_pi(tsm_id, BinderInfo::InstImplicit, ts_m_ty, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, self.type_v.clone(), e);
        b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// pullback_commutes_d : {M : Type u} → {N : Type v} → [TS M] → [TS N] → Prop
    fn build_pullback_commutes_d_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let (n_id, n) = b.fresh_local(self.type_v.clone());
        let ts_m_ty = Expr::app(self.topological_space(self.u_level.clone()), m);
        let (tsm_id, _) = b.fresh_local(ts_m_ty.clone());
        let ts_n_ty = Expr::app(self.topological_space(self.v_level.clone()), n);
        let (tsn_id, _) = b.fresh_local(ts_n_ty.clone());
        let e = b.mk_pi(tsn_id, BinderInfo::InstImplicit, ts_n_ty, self.prop.clone());
        let e = b.mk_pi(tsm_id, BinderInfo::InstImplicit, ts_m_ty, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, self.type_v.clone(), e);
        b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// harmonic_rep : {M} → [TS M] → (dim : Nat) → (k : Nat) → Prop
    fn build_harmonic_rep_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), m);
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let nat_ty = self.nat_const();
        let (dim_id, _) = b.fresh_local(nat_ty.clone());
        let (k_id, _) = b.fresh_local(nat_ty.clone());
        let e = b.mk_pi(k_id, BinderInfo::Default, nat_ty.clone(), self.prop.clone());
        let e = b.mk_pi(dim_id, BinderInfo::Default, nat_ty, e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = DeRhamCtx::new();
    let nat_const = ctx.nat_const();
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let nat_sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
    let nat_one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let mut decls = Vec::with_capacity(DECL_COUNT);

    // SmoothManifold : Type u → Nat → Type u
    decls.push(ctx.to_axiom_u(
        "Topology.DeRham.SmoothManifold",
        Expr::pi(
            BinderInfo::Default,
            ctx.type_u.clone(),
            Expr::pi(BinderInfo::Default, nat_const.clone(), ctx.type_u.clone()),
        ),
    ));

    // DifferentialForm : {M : Type u} → [TS M] → (dim : Nat) → (k : Nat) → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(ctx.type_u.clone());
        let ts_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m);
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let (dim_id, _) = b.fresh_local(nat_const.clone());
        let (k_id, _) = b.fresh_local(nat_const.clone());
        let e = b.mk_pi(
            k_id,
            BinderInfo::Default,
            nat_const.clone(),
            ctx.type_u.clone(),
        );
        let e = b.mk_pi(dim_id, BinderInfo::Default, nat_const.clone(), e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let ty = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom_u("Topology.DeRham.DifferentialForm", ty));
    }

    // exterior_derivative : Ω^k(M) → Ω^(k+1)(M)
    decls.push(ctx.to_axiom_u(
        "Topology.DeRham.exterior_derivative",
        ctx.build_form_to_ret(|_m, _ts, _dim, k| {
            let b2 = EnvDeclBuilder::new();
            let _ = b2; // just need the mathverse constructor
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(ctx.differential_form(), _m.clone()), _ts.clone()),
                    _dim.clone(),
                ),
                Expr::app(nat_succ.clone(), k.clone()),
            )
        }),
    ));

    // 7 declarations sharing {M} → [TS M] → {dim} → {k} → Prop
    let ts_dk_prop = ctx.build_ts_dk_prop();
    for name in [
        "Topology.DeRham.d_squared_zero",
        "Topology.DeRham.wedge_anticommutative",
        "Topology.DeRham.leibniz_rule",
        "Topology.DeRham.exact_is_closed",
        "Topology.DeRham.stokes_theorem",
        "Topology.DeRham.hodge_involution",
        "Topology.DeRham.hodge_decomposition",
    ] {
        decls.push(ctx.to_axiom_u(name, ts_dk_prop.clone()));
    }

    // wedge
    decls.push(ctx.to_axiom_u("Topology.DeRham.wedge", ctx.build_wedge_type()));

    // ClosedForm, ExactForm, HarmonicForm : Ω^k(M) → Prop
    for name in [
        "Topology.DeRham.ClosedForm",
        "Topology.DeRham.ExactForm",
        "Topology.DeRham.HarmonicForm",
    ] {
        decls.push(ctx.to_axiom_u(name, ctx.build_form_to_ret(|_, _, _, _| ctx.prop.clone())));
    }

    // H : (k : Nat) → {M : Type u} → [TS M] → (dim : Nat) → Type u
    decls.push(ctx.to_axiom_u(
        "Topology.DeRham.H",
        ctx.build_nat_ts_dim_type(ctx.type_u.clone()),
    ));

    // H_is_add_comm_group
    decls.push(ctx.to_axiom_u(
        "Topology.DeRham.H_is_add_comm_group",
        ctx.build_h_is_add_comm_group_type(),
    ));

    // derham_theorem : (k : Nat) → {M : Type u} → [TS M] → (dim : Nat) → Prop
    decls.push(ctx.to_axiom_u(
        "Topology.DeRham.derham_theorem",
        ctx.build_nat_ts_dim_type(ctx.prop.clone()),
    ));

    // poincare_lemma
    decls.push(ctx.to_axiom_u(
        "Topology.DeRham.poincare_lemma",
        ctx.build_poincare_lemma_type(),
    ));

    // integrate : Ω^k(M) → Rat
    decls.push(ctx.to_axiom_u(
        "Topology.DeRham.integrate",
        ctx.build_form_to_ret(|_, _, _, _| ctx.rat_const()),
    ));

    // pullback (dual-universe)
    decls.push(ctx.to_axiom_uv("Topology.DeRham.pullback", ctx.build_pullback_type()));

    // pullback_commutes_d (dual-universe)
    decls.push(ctx.to_axiom_uv(
        "Topology.DeRham.pullback_commutes_d",
        ctx.build_pullback_commutes_d_type(),
    ));

    // HodgeStar : Ω^k(M) → Ω^(dim-k)(M)
    decls.push(ctx.to_axiom_u(
        "Topology.DeRham.HodgeStar",
        ctx.build_form_to_ret(|m, ts, dim, k| {
            let dim_minus_k = Expr::app(Expr::app(nat_sub.clone(), dim.clone()), k.clone());
            ctx.mathverse(m, ts, dim, &dim_minus_k)
        }),
    ));

    // codifferential : Ω^k(M) → Ω^(k-1)(M)
    decls.push(ctx.to_axiom_u(
        "Topology.DeRham.codifferential",
        ctx.build_form_to_ret(|m, ts, dim, k| {
            let k_minus_1 = Expr::app(Expr::app(nat_sub.clone(), k.clone()), nat_one.clone());
            ctx.mathverse(m, ts, dim, &k_minus_1)
        }),
    ));

    // Laplacian : Ω^k(M) → Ω^k(M)
    decls.push(ctx.to_axiom_u(
        "Topology.DeRham.Laplacian",
        ctx.build_form_to_ret(|m, ts, dim, k| ctx.mathverse(m, ts, dim, k)),
    ));

    // harmonic_rep
    decls.push(ctx.to_axiom_u(
        "Topology.DeRham.harmonic_rep",
        ctx.build_harmonic_rep_type(),
    ));

    // betti : (k : Nat) → {M : Type u} → [TS M] → (dim : Nat) → Nat
    decls.push(ctx.to_axiom_u(
        "Topology.DeRham.betti",
        ctx.build_nat_ts_dim_type(ctx.nat_const()),
    ));

    // mayer_vietoris : {M : Type u} → [TS M] → Prop
    decls.push(ctx.to_axiom_u(
        "Topology.DeRham.mayer_vietoris",
        ctx.build_ts_type_u(ctx.prop.clone()),
    ));

    debug_assert_eq!(
        decls.len(),
        DECL_COUNT,
        "payload size mismatch for {NAMESPACE}"
    );
    debug_assert_eq!(
        decls.iter().map(|c| c.name.to_string()).collect::<Vec<_>>(),
        DECL_NAMES.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
        "payload names mismatch for {NAMESPACE}"
    );

    decls
}

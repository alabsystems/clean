// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Incremental topology declaration validation harness for tests.
//!
//! This helper replays the TopologicalSpace declarations in deterministic order,
//! collecting all declaration failures in one run instead of stopping at the first gate.

use super::*;

fn declaration_name(decl: &Declaration) -> Name {
    match decl {
        Declaration::Definition { name, .. }
        | Declaration::Axiom { name, .. }
        | Declaration::Theorem { name, .. }
        | Declaration::Opaque { name, .. } => name.clone(),
    }
}

fn format_decl_error(name: &Name, err: &EnvError) -> String {
    match err {
        EnvError::TypeCheckFailed { source, .. } => {
            format!("{}: {:?}", name, source)
        }
        _ => format!("{}: {:?}", name, err),
    }
}

fn init_topological_space_prereqs(env: &mut Environment, include_metric_to_topology: bool) {
    env.init_and().expect("init_and dependency should succeed");
    env.init_exists()
        .expect("init_exists dependency should succeed");
    env.init_true_false()
        .expect("init_true_false dependency should succeed");
    env.init_iff().expect("init_iff dependency should succeed");

    if include_metric_to_topology {
        env.init_metric_space()
            .expect("init_metric_space dependency should succeed");
    }
}

fn topological_space_decl_templates(include_metric_to_topology: bool) -> Vec<Declaration> {
    let mut decls = Vec::new();
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let u_level = Level::param(u.clone());
    let v_level = Level::param(v.clone());
    let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // ================================================================
    // TopologicalSpace : Type u → Type u
    //
    // A typeclass representing a topological space structure on a type.
    // The underlying data is the collection of open sets.
    // ================================================================

    let topological_space_type = Expr::pi(
        BinderInfo::Default,
        type_u.clone(), // α : Type u
        type_u.clone(), // Type u
    );

    decls.push(Declaration::Axiom {
        name: Name::from_string("TopologicalSpace"),
        level_params: vec![u.clone()],
        type_: topological_space_type,
    });

    let topological_space =
        |lvl: Level| Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl]);

    // ================================================================
    // IsOpen : {α : Type u} → [TopologicalSpace α] → (α → Prop) → Prop
    //
    // Predicate indicating a subset (represented as α → Prop) is open.
    // ================================================================

    let is_open_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(), // {α : Type u}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), Expr::bvar(0)), // [TopologicalSpace α]
            Expr::pi(
                BinderInfo::Default,
                Expr::pi(BinderInfo::Default, Expr::bvar(1), prop.clone()), // s : α → Prop
                prop.clone(),
            ),
        ),
    );

    decls.push(Declaration::Axiom {
        name: Name::from_string("IsOpen"),
        level_params: vec![u.clone()],
        type_: is_open_type,
    });

    let is_open_const = Expr::const_(Name::from_string("IsOpen"), vec![u_level.clone()]);

    // Helper: IsOpen {α} [inst] s
    let is_open_app = |alpha_idx: u32, inst_idx: u32, s_idx: u32| {
        Expr::app(
            Expr::app(
                Expr::app(is_open_const.clone(), Expr::bvar(alpha_idx)),
                Expr::bvar(inst_idx),
            ),
            Expr::bvar(s_idx),
        )
    };

    // ================================================================
    // IsClosed : {α : Type u} → [TopologicalSpace α] → (α → Prop) → Prop
    //
    // Predicate indicating a subset is closed (complement is open).
    // ================================================================

    let is_closed_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(), // {α : Type u}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), Expr::bvar(0)), // [TopologicalSpace α]
            Expr::pi(
                BinderInfo::Default,
                Expr::pi(BinderInfo::Default, Expr::bvar(1), prop.clone()), // s : α → Prop
                prop.clone(),
            ),
        ),
    );

    decls.push(Declaration::Axiom {
        name: Name::from_string("IsClosed"),
        level_params: vec![u.clone()],
        type_: is_closed_type,
    });

    let is_closed_const = Expr::const_(Name::from_string("IsClosed"), vec![u_level.clone()]);

    // Helper: IsClosed {α} [inst] s
    let is_closed_app = |alpha_idx: u32, inst_idx: u32, s_idx: u32| {
        Expr::app(
            Expr::app(
                Expr::app(is_closed_const.clone(), Expr::bvar(alpha_idx)),
                Expr::bvar(inst_idx),
            ),
            Expr::bvar(s_idx),
        )
    };

    // ================================================================
    // IsOpen.univ : {α : Type u} → [TopologicalSpace α] → IsOpen (fun _ => True)
    //
    // The whole space is open.
    // ================================================================

    let true_const = Expr::const_(Name::from_string("True"), vec![]);

    // fun _ : α => True
    // After binding {α} [inst]: bvar(1) = α, bvar(0) = inst
    // Inside lambda: bvar(2) = α, bvar(1) = inst, bvar(0) = _
    let univ_set = Expr::lam(BinderInfo::Default, Expr::bvar(1), true_const.clone());

    let is_open_univ_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(), // {α : Type u}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), Expr::bvar(0)), // [TopologicalSpace α]
            Expr::app(
                Expr::app(
                    Expr::app(is_open_const.clone(), Expr::bvar(1)),
                    Expr::bvar(0),
                ),
                univ_set,
            ),
        ),
    );

    decls.push(Declaration::Axiom {
        name: Name::from_string("IsOpen.univ"),
        level_params: vec![u.clone()],
        type_: is_open_univ_type,
    });

    // ================================================================
    // IsOpen.empty : {α : Type u} → [TopologicalSpace α] → IsOpen (fun _ => False)
    //
    // The empty set is open.
    // ================================================================

    let false_const = Expr::const_(Name::from_string("False"), vec![]);

    // fun _ : α => False
    let empty_set = Expr::lam(BinderInfo::Default, Expr::bvar(1), false_const.clone());

    let is_open_empty_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(), // {α : Type u}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), Expr::bvar(0)), // [TopologicalSpace α]
            Expr::app(
                Expr::app(
                    Expr::app(is_open_const.clone(), Expr::bvar(1)),
                    Expr::bvar(0),
                ),
                empty_set,
            ),
        ),
    );

    decls.push(Declaration::Axiom {
        name: Name::from_string("IsOpen.empty"),
        level_params: vec![u.clone()],
        type_: is_open_empty_type,
    });

    // ================================================================
    // IsOpen.inter : {α : Type u} → [TopologicalSpace α] →
    //   {s t : α → Prop} → IsOpen s → IsOpen t → IsOpen (fun x => s x ∧ t x)
    //
    // Finite intersections of open sets are open.
    // ================================================================

    let and_const = Expr::const_(Name::from_string("And"), vec![]);

    // After binding {α} [inst] {s} {t} (hs : IsOpen s) (ht : IsOpen t):
    // bvar(5) = α, bvar(4) = inst, bvar(3) = s, bvar(2) = t, bvar(1) = hs, bvar(0) = ht
    // Inside lambda for result: bvar(6) = α, ..., bvar(0) = x
    // s x ∧ t x
    let s_x_and_t_x = Expr::app(
        Expr::app(and_const.clone(), Expr::app(Expr::bvar(4), Expr::bvar(0))), // s x
        Expr::app(Expr::bvar(3), Expr::bvar(0)),                               // t x
    );

    // fun x : α => s x ∧ t x
    // lambda type α = bvar(5) at depth 6
    let inter_set = Expr::lam(BinderInfo::Default, Expr::bvar(5), s_x_and_t_x);

    // IsOpen (fun x => s x ∧ t x)
    let is_open_inter_result = Expr::app(
        Expr::app(
            Expr::app(is_open_const.clone(), Expr::bvar(5)),
            Expr::bvar(4),
        ),
        inter_set,
    );

    // IsOpen t (inside 5 pi binders: {α}=4, [inst]=3, {s}=2, {t}=1, hs=0)
    let is_open_t = is_open_app(4, 3, 1);

    // IsOpen s
    let is_open_s = is_open_app(3, 2, 1);

    let is_open_inter_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(), // {α : Type u}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), Expr::bvar(0)), // [TopologicalSpace α]
            Expr::pi(
                BinderInfo::Implicit,
                Expr::pi(BinderInfo::Default, Expr::bvar(1), prop.clone()), // {s : α → Prop}
                Expr::pi(
                    BinderInfo::Implicit,
                    Expr::pi(BinderInfo::Default, Expr::bvar(2), prop.clone()), // {t : α → Prop}
                    Expr::pi(
                        BinderInfo::Default,
                        is_open_s,
                        Expr::pi(BinderInfo::Default, is_open_t, is_open_inter_result),
                    ),
                ),
            ),
        ),
    );

    decls.push(Declaration::Axiom {
        name: Name::from_string("IsOpen.inter"),
        level_params: vec![u.clone()],
        type_: is_open_inter_type,
    });

    // ================================================================
    // IsOpen.union : {α : Type u} → [TopologicalSpace α] →
    //   {ι : Type v} → {U : ι → α → Prop} → (∀ i, IsOpen (U i)) →
    //   IsOpen (fun x => ∃ i, U i x)
    //
    // Arbitrary unions of open sets are open.
    // ================================================================

    let type_v = Expr::sort(Level::succ(v_level.clone())); // Type v = Sort (v+1)

    // Depth analysis for IsOpen.union:
    // Pi {α}(d1) [inst](d2) {ι}(d3) {U}(d4) (hU)(d5) → result(d5)
    //   result contains: λ x(d6) . Exists ι (λ i(d7) . U i x)
    //
    // forall_i_is_open is type of hU, used at depth 4:
    //   d4: U=0, ι=1, inst=2, α=3
    //   Pi i:ι . IsOpen(U i) — domain ι=bvar(1)
    //   Inside forall (d5): i=0, U=1, ι=2, inst=3, α=4
    //     U i = app(bvar(1), bvar(0))
    //     IsOpen α inst (U i) = IsOpen bvar(4) bvar(3) (U i)
    //
    // Result at depth 5: hU=0, U=1, ι=2, inst=3, α=4
    //   λ x:α(d6) . ∃ i:ι, U i x
    //   d6: x=0, hU=1, U=2, ι=3, inst=4, α=5
    //     Exists ι=bvar(3) (λ i:ι=bvar(3) . U i x)
    //   d7: i=0, x=1, hU=2, U=3, ι=4, inst=5, α=6
    //     U i x = app(app(bvar(3), bvar(0)), bvar(1))

    // U i (at depth 5, inside forall_i Pi)
    let u_i = Expr::app(Expr::bvar(1), Expr::bvar(0)); // U=bvar(1), i=bvar(0)
    let is_open_u_i = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("IsOpen"), vec![u_level.clone()]),
                Expr::bvar(4), // α at depth 5
            ),
            Expr::bvar(3), // inst at depth 5
        ),
        u_i,
    );

    // ∀ i : ι, IsOpen (U i)  (at depth 4: ι=bvar(1))
    let forall_i_is_open = Expr::pi(BinderInfo::Default, Expr::bvar(1), is_open_u_i);

    // U i x (at depth 7: U=bvar(3), i=bvar(0), x=bvar(1))
    let u_i_x = Expr::app(Expr::app(Expr::bvar(3), Expr::bvar(0)), Expr::bvar(1));

    // fun i : ι => U i x  (lambda type at depth 6: ι=bvar(3))
    let exists_body = Expr::lam(BinderInfo::Default, Expr::bvar(3), u_i_x);

    // ∃ i : ι, U i x  (at depth 6: ι=bvar(3), ι : Type v = Sort(Succ(v)), so Exists.{Succ(v)})
    let exists_i_u_i_x = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(v_level.clone())],
            ),
            Expr::bvar(3), // ι at depth 6
        ),
        exists_body,
    );

    // fun x : α => ∃ i, U i x  (lambda type at depth 5: α=bvar(4))
    let union_set = Expr::lam(BinderInfo::Default, Expr::bvar(4), exists_i_u_i_x);

    // IsOpen (fun x => ∃ i, U i x)
    let is_open_union_result = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("IsOpen"), vec![u_level.clone()]),
                Expr::bvar(4),
            ),
            Expr::bvar(3),
        ),
        union_set,
    );

    // U : ι → α → Prop (as ι → (α → Prop))
    // At depth 3: ι=bvar(0), inst=bvar(1), α=bvar(2)
    // Inner pi at depth 4: j=bvar(0), ι=bvar(1), inst=bvar(2), α=bvar(3)
    let u_type = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0),                                              // ι
        Expr::pi(BinderInfo::Default, Expr::bvar(3), prop.clone()), // α → Prop
    );

    let is_open_union_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(), // {α : Type u}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), Expr::bvar(0)), // [TopologicalSpace α]
            Expr::pi(
                BinderInfo::Implicit,
                type_v.clone(), // {ι : Type v}
                Expr::pi(
                    BinderInfo::Implicit,
                    u_type, // {U : ι → α → Prop}
                    Expr::pi(BinderInfo::Default, forall_i_is_open, is_open_union_result),
                ),
            ),
        ),
    );

    decls.push(Declaration::Axiom {
        name: Name::from_string("IsOpen.union"),
        level_params: vec![u.clone(), v.clone()],
        type_: is_open_union_type,
    });

    // ================================================================
    // IsClosed.compl : {α : Type u} → [TopologicalSpace α] →
    //   {s : α → Prop} → IsClosed s ↔ IsOpen (fun x => ¬ s x)
    //
    // A set is closed iff its complement is open.
    // ================================================================

    // After binding {α} [inst] {s}:
    // bvar(2) = α, bvar(1) = inst, bvar(0) = s
    // Inside lambda: bvar(3) = α, bvar(2) = inst, bvar(1) = s, bvar(0) = x
    // ¬ s x = s x → False
    let not_s_x = Expr::pi(
        BinderInfo::Default,
        Expr::app(Expr::bvar(1), Expr::bvar(0)), // s x
        false_const.clone(),
    );

    // fun x : α => ¬ s x
    // lambda type at depth 3: α=bvar(2)
    let compl_set = Expr::lam(BinderInfo::Default, Expr::bvar(2), not_s_x);

    // IsOpen (fun x => ¬ s x)
    let is_open_compl = Expr::app(
        Expr::app(
            Expr::app(is_open_const.clone(), Expr::bvar(2)),
            Expr::bvar(1),
        ),
        compl_set,
    );

    // IsClosed s
    let is_closed_s = is_closed_app(2, 1, 0);

    // IsClosed s ↔ IsOpen (fun x => ¬ s x)
    let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
    let closed_compl_iff = Expr::app(Expr::app(iff_const.clone(), is_closed_s), is_open_compl);

    let is_closed_compl_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(), // {α : Type u}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), Expr::bvar(0)), // [TopologicalSpace α]
            Expr::pi(
                BinderInfo::Implicit,
                Expr::pi(BinderInfo::Default, Expr::bvar(1), prop.clone()), // {s : α → Prop}
                closed_compl_iff,
            ),
        ),
    );

    decls.push(Declaration::Axiom {
        name: Name::from_string("IsClosed.compl"),
        level_params: vec![u.clone()],
        type_: is_closed_compl_type,
    });

    // ================================================================
    // Topology.Interior : {α : Type u} → [TopologicalSpace α] →
    //   (α → Prop) → (α → Prop)
    //
    // The interior of a set: largest open subset.
    // ================================================================

    let interior_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(), // {α : Type u}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), Expr::bvar(0)), // [TopologicalSpace α]
            Expr::pi(
                BinderInfo::Default,
                Expr::pi(BinderInfo::Default, Expr::bvar(1), prop.clone()), // s : α → Prop
                Expr::pi(BinderInfo::Default, Expr::bvar(2), prop.clone()), // result: α → Prop
            ),
        ),
    );

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.Interior"),
        level_params: vec![u.clone()],
        type_: interior_type,
    });

    let interior_const = Expr::const_(
        Name::from_string("Topology.Interior"),
        vec![u_level.clone()],
    );

    // ================================================================
    // Topology.Closure : {α : Type u} → [TopologicalSpace α] →
    //   (α → Prop) → (α → Prop)
    //
    // The closure of a set: smallest closed superset.
    // ================================================================

    let closure_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(), // {α : Type u}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), Expr::bvar(0)), // [TopologicalSpace α]
            Expr::pi(
                BinderInfo::Default,
                Expr::pi(BinderInfo::Default, Expr::bvar(1), prop.clone()), // s : α → Prop
                Expr::pi(BinderInfo::Default, Expr::bvar(2), prop.clone()), // result: α → Prop
            ),
        ),
    );

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.Closure"),
        level_params: vec![u.clone()],
        type_: closure_type,
    });

    let closure_const = Expr::const_(Name::from_string("Topology.Closure"), vec![u_level.clone()]);

    // ================================================================
    // Topology.interior_spec : {α : Type u} → [TopologicalSpace α] →
    //   {s : α → Prop} → (x : α) →
    //   Interior s x ↔ ∃ U, IsOpen U ∧ U x ∧ (∀ y, U y → s y)
    //
    // x is in the interior of s iff there's an open neighborhood of x contained in s.
    // ================================================================

    // After binding {α} [inst] {s} (x : α):
    // bvar(3) = α, bvar(2) = inst, bvar(1) = s, bvar(0) = x
    // Interior s x
    let interior_s_x = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(interior_const.clone(), Expr::bvar(3)),
                Expr::bvar(2),
            ),
            Expr::bvar(1),
        ),
        Expr::bvar(0),
    );

    // Inside exists U: bvar(4) = α, bvar(3) = inst, bvar(2) = s, bvar(1) = x, bvar(0) = U
    // IsOpen U
    let is_open_u_spec = Expr::app(
        Expr::app(
            Expr::app(is_open_const.clone(), Expr::bvar(4)),
            Expr::bvar(3),
        ),
        Expr::bvar(0),
    );

    // U x
    let u_x_spec = Expr::app(Expr::bvar(0), Expr::bvar(1));

    // Inside ∀ y: bvar(5) = α, bvar(4) = inst, bvar(3) = s, bvar(2) = x, bvar(1) = U, bvar(0) = y
    // U y → s y
    let u_y_implies_s_y = Expr::pi(
        BinderInfo::Default,
        Expr::app(Expr::bvar(1), Expr::bvar(0)), // U y
        Expr::app(Expr::bvar(4), Expr::bvar(1)), // s y (shifted by the hypothesis binding)
    );

    // ∀ y : α, U y → s y  (at depth 5: α=bvar(4))
    let forall_y_u_implies_s = Expr::pi(BinderInfo::Default, Expr::bvar(4), u_y_implies_s_y);

    // U x ∧ (∀ y, U y → s y)
    let u_x_and_subset = Expr::app(Expr::app(and_const.clone(), u_x_spec), forall_y_u_implies_s);

    // IsOpen U ∧ U x ∧ (∀ y, U y → s y)
    let is_open_and_rest = Expr::app(Expr::app(and_const.clone(), is_open_u_spec), u_x_and_subset);

    // fun U : α → Prop => ...  (lambda type at depth 4: α=bvar(3))
    let exists_body_interior = Expr::lam(
        BinderInfo::Default,
        Expr::pi(BinderInfo::Default, Expr::bvar(3), prop.clone()), // U : α → Prop
        is_open_and_rest,
    );

    // ∃ U : α → Prop, IsOpen U ∧ U x ∧ (∀ y, U y → s y)
    // (α → Prop) : Sort(max(succ u, 1)) = Sort(succ u), so Exists.{succ u}
    let exists_u = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(u_level.clone())],
            ),
            Expr::pi(BinderInfo::Default, Expr::bvar(3), prop.clone()), // α → Prop
        ),
        exists_body_interior,
    );

    // Interior s x ↔ ∃ U, ...
    let interior_spec_iff = Expr::app(Expr::app(iff_const.clone(), interior_s_x), exists_u);

    let interior_spec_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(), // {α : Type u}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), Expr::bvar(0)), // [TopologicalSpace α]
            Expr::pi(
                BinderInfo::Implicit,
                Expr::pi(BinderInfo::Default, Expr::bvar(1), prop.clone()), // {s : α → Prop}
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(2), // x : α
                    interior_spec_iff,
                ),
            ),
        ),
    );

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.interior_spec"),
        level_params: vec![u.clone()],
        type_: interior_spec_type,
    });

    // ================================================================
    // Topology.closure_spec : {α : Type u} → [TopologicalSpace α] →
    //   {s : α → Prop} → (x : α) →
    //   Closure s x ↔ ∀ U, IsOpen U → U x → ∃ y, U y ∧ s y
    //
    // x is in the closure of s iff every open neighborhood of x intersects s.
    // ================================================================

    // After binding {α} [inst] {s} (x : α):
    // bvar(3) = α, bvar(2) = inst, bvar(1) = s, bvar(0) = x
    // Closure s x
    let closure_s_x = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(closure_const.clone(), Expr::bvar(3)),
                Expr::bvar(2),
            ),
            Expr::bvar(1),
        ),
        Expr::bvar(0),
    );

    // Inside ∀ U: bvar(4) = α, bvar(3) = inst, bvar(2) = s, bvar(1) = x, bvar(0) = U
    // IsOpen U
    let is_open_u_closure = Expr::app(
        Expr::app(
            Expr::app(is_open_const.clone(), Expr::bvar(4)),
            Expr::bvar(3),
        ),
        Expr::bvar(0),
    );

    // U x (after IsOpen U hypothesis): bvar(5) = α, bvar(4) = inst, bvar(3) = s, bvar(2) = x, bvar(1) = U, bvar(0) = hopen
    let u_x_closure = Expr::app(Expr::bvar(1), Expr::bvar(2));

    // Inside exists y (after U x hypothesis): bvar(6) = α, bvar(5) = inst, bvar(4) = s, bvar(3) = x, bvar(2) = U, bvar(1) = hopen, bvar(0) = hux
    // Then inside body: bvar(7) = α, ..., bvar(0) = y
    // U y ∧ s y
    let u_y_and_s_y = Expr::app(
        Expr::app(and_const.clone(), Expr::app(Expr::bvar(3), Expr::bvar(0))), // U y
        Expr::app(Expr::bvar(5), Expr::bvar(0)),                               // s y
    );

    // fun y : α => U y ∧ s y  (lambda type at depth 7: α=bvar(6))
    let exists_y_body = Expr::lam(BinderInfo::Default, Expr::bvar(6), u_y_and_s_y);

    // ∃ y : α, U y ∧ s y  (α : Type u = Sort(u+1), so Exists.{u+1})
    let exists_y = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(u_level.clone())],
            ),
            Expr::bvar(6), // α
        ),
        exists_y_body,
    );

    // U x → ∃ y, U y ∧ s y
    let u_x_implies_exists = Expr::pi(BinderInfo::Default, u_x_closure, exists_y);

    // IsOpen U → U x → ∃ y, U y ∧ s y
    let is_open_implies = Expr::pi(BinderInfo::Default, is_open_u_closure, u_x_implies_exists);

    // ∀ U : α → Prop, IsOpen U → U x → ∃ y, U y ∧ s y  (at depth 4: α=bvar(3))
    let forall_u_closure = Expr::pi(
        BinderInfo::Default,
        Expr::pi(BinderInfo::Default, Expr::bvar(3), prop.clone()), // U : α → Prop
        is_open_implies,
    );

    // Closure s x ↔ ∀ U, ...
    let closure_spec_iff = Expr::app(Expr::app(iff_const.clone(), closure_s_x), forall_u_closure);

    let closure_spec_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(), // {α : Type u}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), Expr::bvar(0)), // [TopologicalSpace α]
            Expr::pi(
                BinderInfo::Implicit,
                Expr::pi(BinderInfo::Default, Expr::bvar(1), prop.clone()), // {s : α → Prop}
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(2), // x : α
                    closure_spec_iff,
                ),
            ),
        ),
    );

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.closure_spec"),
        level_params: vec![u.clone()],
        type_: closure_spec_type,
    });

    // ================================================================
    // Topology.metric_to_topology : {α : Type u} → MetricSpace α → TopologicalSpace α
    //
    // Every metric space has an induced topology (the metric topology).
    // ================================================================

    // Check if MetricSpace is available
    if include_metric_to_topology {
        let metric_space_const =
            Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);

        let metric_to_topology_type = Expr::pi(
            BinderInfo::Implicit,
            type_u.clone(), // {α : Type u}
            Expr::pi(
                BinderInfo::Default,
                Expr::app(metric_space_const.clone(), Expr::bvar(0)), // (inst : MetricSpace α)
                Expr::app(topological_space(u_level.clone()), Expr::bvar(1)), // TopologicalSpace α
            ),
        );

        decls.push(Declaration::Axiom {
            name: Name::from_string("Topology.metric_to_topology"),
            level_params: vec![u.clone()],
            type_: metric_to_topology_type,
        });
    }

    decls
}

fn validate_decls_incremental(
    env: &mut Environment,
    decls: Vec<Declaration>,
) -> Vec<(Name, Option<String>)> {
    let mut results = Vec::new();
    for decl in decls {
        let name = declaration_name(&decl);
        match env.add_decl(decl) {
            Ok(()) => results.push((name, None)),
            Err(err) => {
                // Do NOT add failed declarations via add_decl_unchecked (#1537).
                // Downstream declarations that depend on a broken predecessor should
                // fail too — that's the correct cascading behavior. Adding with
                // unchecked masks real type errors and creates false confidence.
                let formatted = format_decl_error(&name, &err);
                results.push((name, Some(formatted)));
            }
        }
    }

    results
}

pub(super) fn validate_topological_space_decls_incremental(
    include_metric_to_topology: bool,
) -> Vec<(Name, Option<String>)> {
    let mut env = Environment::new();
    init_topological_space_prereqs(&mut env, include_metric_to_topology);
    validate_decls_incremental(
        &mut env,
        topological_space_decl_templates(include_metric_to_topology),
    )
}

pub(super) fn validate_decl_sequence_incremental_for_test(
    decls: Vec<Declaration>,
) -> Vec<(Name, Option<String>)> {
    let mut env = Environment::new();
    validate_decls_incremental(&mut env, decls)
}

pub(super) fn assert_topological_space_decl_validation_passes(include_metric_to_topology: bool) {
    let results = validate_topological_space_decls_incremental(include_metric_to_topology);
    let failures: Vec<String> = results.iter().filter_map(|(_, err)| err.clone()).collect();

    assert!(
        failures.is_empty(),
        "TopologicalSpace declaration validation failures:\n{}",
        failures.join("\n")
    );
}

pub(super) fn init_topological_space_env_through(
    target_decl: &str,
    include_metric_to_topology: bool,
) -> Environment {
    let target_name = Name::from_string(target_decl);
    let mut env = Environment::new();
    init_topological_space_prereqs(&mut env, include_metric_to_topology);

    let mut failures = Vec::new();
    for decl in topological_space_decl_templates(include_metric_to_topology) {
        let name = declaration_name(&decl);
        match env.add_decl(decl) {
            Ok(()) => {}
            Err(err) => {
                let formatted = format_decl_error(&name, &err);
                failures.push(formatted.clone());
                // Do NOT add failed declarations via add_decl_unchecked (#1537).
                // Downstream declarations should see the real environment state,
                // not one polluted with broken types.

                if name == target_name {
                    panic!(
                        "TopologicalSpace target declaration `{target_decl}` failed: {formatted}\nAll failures:\n{}",
                        failures.join("\n")
                    );
                }
            }
        }

        if name == target_name {
            return env;
        }
    }

    panic!("Target declaration `{target_decl}` not found in topological declaration templates");
}

/// Initialize an environment with Continuous declarations up to and including `target_decl`.
///
/// Uses the same `topology_continuous_decl_templates` as the production code.
/// Collects failures for prior declarations but panics if the target itself fails.
pub(super) fn init_topology_continuous_env_through(
    target_decl: &str,
    include_metric_iff: bool,
) -> Environment {
    use super::topology_basic::topology_continuous_decl_templates;

    let target_name = Name::from_string(target_decl);
    let mut env = Environment::new();
    // When metric_iff is needed, MetricSpace must be initialized BEFORE TopologicalSpace
    // so that init_topological_space registers Topology.metric_to_topology.
    if include_metric_iff {
        env.init_metric_continuous()
            .expect("MetricContinuous prereq should succeed for metric_iff");
    }
    // Prerequisites: TopologicalSpace + Iff (same as init_topology_continuous)
    env.init_topological_space()
        .expect("TopologicalSpace prereq should succeed");
    env.init_iff().expect("Iff prereq should succeed");

    let mut failures = Vec::new();
    for decl in topology_continuous_decl_templates(include_metric_iff) {
        let name = declaration_name(&decl);
        match env.add_decl(decl) {
            Ok(()) => {}
            Err(err) => {
                let formatted = format_decl_error(&name, &err);
                failures.push(formatted.clone());
                if name == target_name {
                    panic!(
                        "Continuous target declaration `{target_decl}` failed: {formatted}\nAll failures:\n{}",
                        failures.join("\n")
                    );
                }
            }
        }

        if name == target_name {
            return env;
        }
    }

    panic!("Target declaration `{target_decl}` not found in continuous declaration templates");
}

/// Initialize an environment with Connected declarations up to and including `target_decl`.
///
/// Uses the same `topology_connected_decl_templates` as the production code.
/// Collects failures for prior declarations but panics if the target itself fails.
pub(super) fn init_topology_connected_env_through(target_decl: &str) -> Environment {
    use super::topology_connected::topology_connected_decl_templates;

    let target_name = Name::from_string(target_decl);
    let mut env = Environment::new();
    // Prerequisites: TopologicalSpace + Continuous + Iff + And + Classical
    env.init_topological_space()
        .expect("TopologicalSpace prereq should succeed");
    env.init_topology_continuous()
        .expect("TopologyContinuous prereq should succeed");
    env.init_iff().expect("Iff prereq should succeed");
    env.init_and().expect("And prereq should succeed");
    env.init_classical()
        .expect("Classical prereq should succeed");

    let mut failures = Vec::new();
    for decl in topology_connected_decl_templates() {
        let name = declaration_name(&decl);
        match env.add_decl(decl) {
            Ok(()) => {}
            Err(err) => {
                let formatted = format_decl_error(&name, &err);
                failures.push(formatted.clone());
                if name == target_name {
                    panic!(
                        "Connected target declaration `{target_decl}` failed: {formatted}\nAll failures:\n{}",
                        failures.join("\n")
                    );
                }
            }
        }

        if name == target_name {
            return env;
        }
    }

    panic!("Target declaration `{target_decl}` not found in connected declaration templates");
}

/// Initialize an environment with Compact declarations up to and including `target_decl`.
///
/// Uses the same `topology_compact_decl_templates` as the production code.
/// Collects failures for prior declarations but panics if the target itself fails.
pub(super) fn init_topology_compact_env_through(
    target_decl: &str,
    include_metric_iff: bool,
) -> Environment {
    use super::topology_compact::topology_compact_decl_templates;

    let target_name = Name::from_string(target_decl);
    let mut env = Environment::new();
    // When metric_iff is needed, MetricSpace and Metric.Compact must be initialized
    // BEFORE TopologicalSpace so that init_topological_space registers metric_to_topology.
    if include_metric_iff {
        env.init_metric_compact()
            .expect("MetricCompact prereq should succeed for metric_iff");
    }
    // Prerequisites: TopologicalSpace + Continuous + Iff + And + Exists
    env.init_topological_space()
        .expect("TopologicalSpace prereq should succeed");
    env.init_topology_continuous()
        .expect("TopologyContinuous prereq should succeed");
    env.init_iff().expect("Iff prereq should succeed");
    env.init_and().expect("And prereq should succeed");
    env.init_exists().expect("Exists prereq should succeed");

    let mut failures = Vec::new();
    for decl in topology_compact_decl_templates(include_metric_iff) {
        let name = declaration_name(&decl);
        match env.add_decl(decl) {
            Ok(()) => {}
            Err(err) => {
                let formatted = format_decl_error(&name, &err);
                failures.push(formatted.clone());
                if name == target_name {
                    panic!(
                        "Compact target declaration `{target_decl}` failed: {formatted}\nAll failures:\n{}",
                        failures.join("\n")
                    );
                }
            }
        }

        if name == target_name {
            return env;
        }
    }

    panic!("Target declaration `{target_decl}` not found in compact declaration templates");
}

/// Initialize an environment with Hausdorff declarations up to and including `target_decl`.
///
/// Uses the same `topology_hausdorff_decl_templates` as the production code.
/// Collects failures for prior declarations but panics if the target itself fails.
pub(super) fn init_topology_hausdorff_env_through(
    target_decl: &str,
    include_compact: bool,
    include_metric: bool,
) -> Environment {
    use super::topology_hausdorff::topology_hausdorff_decl_templates;

    let target_name = Name::from_string(target_decl);
    let mut env = Environment::new();
    // When compact is needed, initialize Compact before Hausdorff
    if include_compact {
        env.init_topology_compact()
            .expect("TopologyCompact prereq should succeed for include_compact");
    }
    // When metric is needed, initialize MetricSpace before Hausdorff
    if include_metric {
        env.init_metric_space()
            .expect("MetricSpace prereq should succeed for include_metric");
    }
    // Prerequisites (same as init_topology_hausdorff)
    env.init_topological_space()
        .expect("TopologicalSpace prereq should succeed");
    env.init_iff().expect("Iff prereq should succeed");
    env.init_and().expect("And prereq should succeed");
    env.init_exists().expect("Exists prereq should succeed");
    env.init_true_false()
        .expect("TrueFalse prereq should succeed");
    env.init_eq().expect("Eq prereq should succeed");

    let mut failures = Vec::new();
    for decl in topology_hausdorff_decl_templates(include_compact, include_metric) {
        let name = declaration_name(&decl);
        match env.add_decl(decl) {
            Ok(()) => {}
            Err(err) => {
                let formatted = format_decl_error(&name, &err);
                failures.push(formatted.clone());
                if name == target_name {
                    panic!(
                        "Hausdorff target declaration `{target_decl}` failed: {formatted}\nAll failures:\n{}",
                        failures.join("\n")
                    );
                }
            }
        }

        if name == target_name {
            return env;
        }
    }

    panic!("Target declaration `{target_decl}` not found in hausdorff declaration templates");
}

/// Incremental env_through harness for Topology.Homeomorphism declarations.
///
/// Replays declarations from `topology_homeomorphism_decl_templates` up to and including
/// `target_decl`, stopping early. Conditional declarations are controlled by:
/// - `include_connected`: adds `Topology.homeomorphism_connected` (requires Connected init)
/// - `include_compact`: adds `Topology.homeomorphism_compact` (requires Compact init)
pub(super) fn init_topology_homeomorphism_env_through(
    target_decl: &str,
    include_connected: bool,
    include_compact: bool,
) -> Environment {
    use super::topology_homeomorphism::topology_homeomorphism_decl_templates;

    let target_name = Name::from_string(target_decl);
    let mut env = Environment::new();
    // When connected is needed, initialize Connected before Homeomorphism
    if include_connected {
        env.init_topology_connected()
            .expect("TopologyConnected prereq should succeed for include_connected");
    }
    // When compact is needed, initialize Compact before Homeomorphism
    if include_compact {
        env.init_topology_compact()
            .expect("TopologyCompact prereq should succeed for include_compact");
    }
    // Prerequisites (same as init_topology_homeomorphism)
    env.init_topology_continuous()
        .expect("TopologyContinuous prereq should succeed");
    env.init_and().expect("And prereq should succeed");
    env.init_eq().expect("Eq prereq should succeed");
    env.init_iff().expect("Iff prereq should succeed");

    let mut failures = Vec::new();
    for decl in topology_homeomorphism_decl_templates(include_connected, include_compact) {
        let name = declaration_name(&decl);
        match env.add_decl(decl) {
            Ok(()) => {}
            Err(err) => {
                let formatted = format_decl_error(&name, &err);
                failures.push(formatted.clone());
                if name == target_name {
                    panic!(
                        "Homeomorphism target declaration `{target_decl}` failed: {formatted}\nAll failures:\n{}",
                        failures.join("\n")
                    );
                }
            }
        }

        if name == target_name {
            return env;
        }
    }

    panic!("Target declaration `{target_decl}` not found in homeomorphism declaration templates");
}

/// Incrementally replay LocallyCompact declarations up to `target_decl`.
///
/// Prerequisites: TopologyCompact (brings TopologicalSpace, Continuous, IsCompactSet),
/// And, Exists.
///
/// No conditional declarations — all 3 declarations are always present.
pub(super) fn init_topology_locally_compact_env_through(target_decl: &str) -> Environment {
    use super::topology_compact::topology_locally_compact_decl_templates;

    let target_name = Name::from_string(target_decl);
    let mut env = Environment::new();
    // Prerequisites (same as init_topology_locally_compact)
    env.init_topology_compact()
        .expect("TopologyCompact prereq should succeed");
    env.init_and().expect("And prereq should succeed");
    env.init_exists().expect("Exists prereq should succeed");

    let mut failures = Vec::new();
    for decl in topology_locally_compact_decl_templates() {
        let name = declaration_name(&decl);
        match env.add_decl(decl) {
            Ok(()) => {}
            Err(err) => {
                let formatted = format_decl_error(&name, &err);
                failures.push(formatted.clone());
                if name == target_name {
                    panic!(
                        "LocallyCompact target declaration `{target_decl}` failed: {formatted}\nAll failures:\n{}",
                        failures.join("\n")
                    );
                }
            }
        }

        if name == target_name {
            return env;
        }
    }

    panic!("Target declaration `{target_decl}` not found in locally_compact declaration templates");
}

/// Incrementally replay PathConnected overlay constants up to `target_decl`.
///
/// Uses the generated overlay payload (same constants as production
/// `init_topology_path_connected`), loading one `ConstantInfo` at a time
/// via `extend_constants_unchecked` so individual constant tests can isolate
/// failures to a single declaration.
///
/// Prerequisites: Continuous, Connected, Eq, Iff, Exists.
pub(super) fn init_topology_path_connected_env_through(target_decl: &str) -> Environment {
    use super::generated::topology_path_connected;

    let target_name = Name::from_string(target_decl);
    let mut env = Environment::new();
    // Same prerequisites as init_topology_path_connected
    env.init_topology_continuous()
        .expect("Continuous prereq should succeed");
    env.init_topology_connected()
        .expect("Connected prereq should succeed");
    env.init_eq().expect("Eq prereq should succeed");
    env.init_iff().expect("Iff prereq should succeed");
    env.init_exists().expect("Exists prereq should succeed");

    for info in topology_path_connected::payload() {
        let name = info.name.clone();
        env.extend_constants_unchecked(std::iter::once(info));
        if name == target_name {
            return env;
        }
    }

    panic!("Target declaration `{target_decl}` not found in path_connected overlay payload");
}

/// Incrementally replay SimplyConnected overlay constants up to `target_decl`.
///
/// Prerequisites: PathConnected, And, Iff, Exists.
pub(super) fn init_topology_simply_connected_env_through(target_decl: &str) -> Environment {
    use super::generated::topology_simply_connected;

    let target_name = Name::from_string(target_decl);
    let mut env = Environment::new();
    env.init_topology_path_connected()
        .expect("PathConnected prereq should succeed");
    env.init_and().expect("And prereq should succeed");
    env.init_iff().expect("Iff prereq should succeed");
    env.init_exists().expect("Exists prereq should succeed");

    for info in topology_simply_connected::payload() {
        let name = info.name.clone();
        env.extend_constants_unchecked(std::iter::once(info));
        if name == target_name {
            return env;
        }
    }

    panic!("Target declaration `{target_decl}` not found in simply_connected overlay payload");
}

/// Incrementally replay Contractible overlay constants up to `target_decl`.
///
/// Prerequisites: SimplyConnected, Exists, Classical (Nonempty).
pub(super) fn init_topology_contractible_env_through(target_decl: &str) -> Environment {
    use super::generated::topology_contractible;

    let target_name = Name::from_string(target_decl);
    let mut env = Environment::new();
    env.init_topology_simply_connected()
        .expect("SimplyConnected prereq should succeed");
    env.init_exists().expect("Exists prereq should succeed");
    env.init_classical()
        .expect("Classical prereq should succeed");

    for info in topology_contractible::payload() {
        let name = info.name.clone();
        env.extend_constants_unchecked(std::iter::once(info));
        if name == target_name {
            return env;
        }
    }

    panic!("Target declaration `{target_decl}` not found in contractible overlay payload");
}

/// Incrementally replay CoveringSpace overlay constants up to `target_decl`.
///
/// Prerequisites: PathConnected, Homeomorphism, Exists, And, Iff.
pub(super) fn init_topology_covering_space_env_through(target_decl: &str) -> Environment {
    use super::generated::topology_covering_space;

    let target_name = Name::from_string(target_decl);
    let mut env = Environment::new();
    env.init_topology_path_connected()
        .expect("PathConnected prereq should succeed");
    env.init_topology_homeomorphism()
        .expect("Homeomorphism prereq should succeed");
    env.init_exists().expect("Exists prereq should succeed");
    env.init_and().expect("And prereq should succeed");
    env.init_iff().expect("Iff prereq should succeed");

    for info in topology_covering_space::payload() {
        let name = info.name.clone();
        env.extend_constants_unchecked(std::iter::once(info));
        if name == target_name {
            return env;
        }
    }

    panic!("Target declaration `{target_decl}` not found in covering_space overlay payload");
}

/// Incrementally replay FundamentalGroup overlay constants up to `target_decl`.
///
/// Prerequisites: SimplyConnected, PathConnected, Eq, Iff.
pub(super) fn init_topology_fundamental_group_env_through(target_decl: &str) -> Environment {
    use super::generated::topology_fundamental_group;

    let target_name = Name::from_string(target_decl);
    let mut env = Environment::new();
    env.init_topology_simply_connected()
        .expect("SimplyConnected prereq should succeed");
    env.init_topology_path_connected()
        .expect("PathConnected prereq should succeed");
    env.init_eq().expect("Eq prereq should succeed");
    env.init_iff().expect("Iff prereq should succeed");

    for info in topology_fundamental_group::payload() {
        let name = info.name.clone();
        env.extend_constants_unchecked(std::iter::once(info));
        if name == target_name {
            return env;
        }
    }

    panic!("Target declaration `{target_decl}` not found in fundamental_group overlay payload");
}

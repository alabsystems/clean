// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Up-front dependency-ordered registration helpers for the closure-replay
//! driver: topological ordering plus the class / method / instance-op /
//! list-fn / poly-inst registries.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::Environment;

use super::super::isabelle_pure::IsaProvenTheorem;
use super::super::isabelle_pure_translate::{
    alt_def_head, class_def_superclasses, isa_shape_key, register_class_def, register_inst_link,
    register_instance_op_def, register_list_fn_def, register_method_defs, register_method_inst_def,
    register_poly_inst_def_guarded, ClassRegistry, InstanceOpRegistry, ListFnRegistry,
    MethodRegistry, PolyInstRegistry,
};

/// Order theorems so every in-batch `PThm` dependency precedes its user
/// (Kahn's algorithm over the serial graph). Theorems referencing serials not
/// present in the batch keep their relative order; the missing dep simply fails
/// to resolve at translate time (honest rejection).
pub(super) fn topological_order(theorems: &[IsaProvenTheorem]) -> Vec<usize> {
    let index_of: BTreeMap<i64, usize> = theorems
        .iter()
        .enumerate()
        .filter(|(_, t)| t.serial != 0)
        .map(|(i, t)| (t.serial, i))
        .collect();

    // Edges: dep -> user. In-degree counts only in-batch deps.
    let mut deps_in_batch: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); theorems.len()];
    for (i, t) in theorems.iter().enumerate() {
        let mut serials = Vec::new();
        t.proof.thm_deps(&mut serials);
        for s in serials {
            if let Some(&j) = index_of.get(&s) {
                if j != i {
                    deps_in_batch[i].insert(j);
                }
            }
        }
    }

    let mut indeg: Vec<usize> = deps_in_batch.iter().map(BTreeSet::len).collect();
    let mut ready: Vec<usize> = (0..theorems.len()).filter(|&i| indeg[i] == 0).collect();
    let mut order = Vec::with_capacity(theorems.len());
    let mut emitted = vec![false; theorems.len()];

    while let Some(i) = ready.pop() {
        if emitted[i] {
            continue;
        }
        emitted[i] = true;
        order.push(i);
        for (j, deps) in deps_in_batch.iter().enumerate() {
            if !emitted[j] && deps.contains(&i) {
                indeg[j] -= 1;
                if indeg[j] == 0 {
                    ready.push(j);
                }
            }
        }
    }
    // Any remaining (in a dependency cycle — shouldn't happen for real proofs)
    // are appended; they will simply fail to resolve and be rejected.
    for (i, &done) in emitted.iter().enumerate() {
        if !done {
            order.push(i);
        }
    }
    order
}

/// Register every structured type-class definition in the batch into `env` and
/// `registry`, in **superclass-first order**.
///
/// The `…c_class_def` axioms carry no `PThm` dependencies (their proofs are bare
/// `PAxm` leaves), so the closure topological sort imposes no order among them.
/// But a class whose body re-embeds a structured superclass's operations
/// (`ab_semigroup_add` over `semigroup_add`, `monoid_add` over
/// `semigroup_add`/`zero`, …) can only be built **faithfully** once that
/// superclass is already registered: otherwise its `super_class TYPE('a)`
/// membership conjunct erases to the vacuous `True` (dropping the inherited
/// axioms — an unfaithful, weaker membership proposition) and the inherited
/// operations cannot be typed (so `build_class_def` fails outright). A fixpoint
/// worklist registers each class as soon as all its superclass dependencies are
/// in the registry, so the membership proposition always contains the real
/// (recursively unfolded) superclass axioms.
pub(super) fn register_classes_superclass_first(
    theorems: &[IsaProvenTheorem],
    env: &mut Environment,
    registry: &mut ClassRegistry,
) {
    // Collect the class-def theorems with their (own-name, superclass-deps), and
    // the set of class names actually defined in this batch.
    let mut pending: Vec<(usize, Vec<String>)> = Vec::new();
    let mut defined_here: BTreeSet<String> = BTreeSet::new();
    for (i, t) in theorems.iter().enumerate() {
        if let Some((own, supers)) = class_def_superclasses(t) {
            defined_here.insert(own);
            pending.push((i, supers));
        }
    }

    // Repeatedly register every class all of whose *in-batch* superclasses are
    // already registered, until a full sweep makes no progress. A class whose
    // superclass is absent from the batch (or itself unregistrable) is attempted
    // once at the end — `register_class_def` simply returns `None`/erases and the
    // class falls back to `True`, exactly as before.
    let mut changed = true;
    while changed {
        changed = false;
        pending.retain(|(i, supers)| {
            let ready = supers.iter().all(|s| {
                // A superclass dep is satisfied if it is registered, or if it is
                // a base sort with no registrable class-def in this batch at all
                // (so waiting on it would never make progress).
                registry.contains_key(s) || !defined_here.contains(s)
            });
            if !ready {
                return true; // keep for a later sweep
            }
            if let Some((class_name, def_decl, info)) = register_class_def(&theorems[*i], registry)
            {
                if env.add_decl(def_decl).is_ok() {
                    registry.insert(class_name, info);
                }
            }
            changed = true;
            false // done with this one
        });
    }
    // Any classes left in a cycle (should not happen for real class hierarchies)
    // or with a permanently-unregistrable superclass: attempt once, best-effort.
    for (i, _supers) in pending {
        if let Some((class_name, def_decl, info)) = register_class_def(&theorems[i], registry) {
            if env.add_decl(def_decl).is_ok() {
                registry.insert(class_name, info);
            }
        }
    }
}

/// Register every **overloaded class method** whose `…_dict` dictionary axiom
/// appears anywhere in the batch, as a clean polymorphic `Definition` (the
/// operational analogue of [`register_classes_superclass_first`]).
///
/// Each `c_class.method` (`numeral`, `of_nat`, `power`, `dvd`, `sum`, `max`,
/// `min`, …) is overloaded; its `…_dict` axiom `c_class.method ≡ c.method ops`
/// is exported only as a bare `PAxm` argument to `Pure.symmetric` inside consumer
/// proofs (never standalone — see [`super::isabelle_pure_translate::MethodDefInfo`]).
/// We scan every proof for those spines, build the method's `Definition`
/// (`isabelle.method.<c> := λ(α)(impl)(ops). impl ops`), and register it so that:
/// (1) every occurrence of the overloaded method in a consumer's statement/proof
/// embeds to that def-const (δ-unfolding to its dictionary form), and (2) the
/// `…_dict` axiom verifies reflexively. Registration is idempotent (the first
/// recovered equation per method wins); a method whose `Definition` the kernel
/// rejects (`add_decl` fails) is simply left unregistered, so its `…_dict` stays
/// `unmapped-axiom` exactly as before — never mis-verified.
pub(super) fn register_methods(
    theorems: &[IsaProvenTheorem],
    env: &mut Environment,
    registry: &mut MethodRegistry,
) {
    for thm in theorems {
        for (method_name, def_decl, info) in register_method_defs(thm, registry) {
            if env.add_decl(def_decl).is_ok() {
                registry.insert(method_name, info);
            }
        }
    }
}

/// Register every **monomorphic ground-type instance operation** whose
/// recursive-arithmetic `…_nat_def` / `…_num_def` axiom appears in the batch, as
/// a clean `Definition`, in **serial (= dependency) order**.
///
/// The instance-op definitions on `Nat.nat` / `Num.num` form a dependency chain:
/// `Nat.times_nat_def`'s body mentions `Nat.plus_nat` and the `0::nat` base, so
/// `plus` (and the directly-mapped `0::nat`) must be in the registry before
/// `times` is built (otherwise `times`'s body would not close and registration
/// would skip it). Isabelle serials are assigned in creation order, and a
/// definition's body only ever mentions operations defined *earlier*, so the
/// serials of the bodies' dependencies are strictly smaller — sorting by serial
/// presents every op after the ones its body uses (the same deps-before-uses
/// invariant the streaming driver relies on). A theorem with serial `0` (rare
/// anonymous node) is treated as latest (its instance-op def, if any, is built
/// last); the `register_instance_op_def` close-or-skip guard keeps it honest.
pub(super) fn register_instance_ops(
    theorems: &[IsaProvenTheorem],
    env: &mut Environment,
    registry: &mut InstanceOpRegistry,
) {
    // Build over the def axioms in ascending serial order so a base op is
    // registered before any recursive op whose body references it.
    let mut order: Vec<usize> = (0..theorems.len()).collect();
    order.sort_by_key(|&i| theorems[i].serial);
    for &i in &order {
        if let Some((key, def_decl, info)) = register_instance_op_def(&theorems[i], registry) {
            if env.add_decl(def_decl).is_ok() {
                registry.insert(key, info);
            }
        }
    }
}

/// Register every **plain polymorphic list (datatype) function** whose recursive
/// `List.*_def` axiom appears in the batch, as a clean polymorphic `Definition`,
/// in **serial (= dependency) order**.
///
/// The list-function definitions form a dependency chain (`List.rev`'s body
/// mentions `List.append`, so `append` must be registered before `rev` is built —
/// else `rev`'s body would not close and registration would skip it). Isabelle
/// serials are creation-ordered and a definition's body only mentions functions
/// defined earlier, so sorting by serial presents every function after the ones
/// its body uses (the same deps-before-uses invariant the other registries use).
/// The `register_list_fn_def` close-or-skip guard keeps every registration
/// honest; the kernel re-checks each `Definition` via `add_decl`.
pub(super) fn register_list_fns(
    theorems: &[IsaProvenTheorem],
    env: &mut Environment,
    registry: &mut ListFnRegistry,
    instance_ops: &InstanceOpRegistry,
    methods: &MethodRegistry,
) {
    let mut order: Vec<usize> = (0..theorems.len()).collect();
    order.sort_by_key(|&i| theorems[i].serial);
    for &i in &order {
        if let Some((key, def_decl, info)) =
            register_list_fn_def(&theorems[i], registry, instance_ops, methods)
        {
            if env.add_decl(def_decl).is_ok() {
                registry.insert(key, info);
            }
        }
    }
}

/// Register every **polymorphic instance operation** whose `_def` axiom appears in
/// the batch (`Int.power_int`, …), as a clean polymorphic `Definition`, in **serial
/// (= dependency) order**.
///
/// These are the type-class-method-using generalisation of the ground instance ops:
/// the constant is polymorphic (`'a`-generic) and its body uses overloaded class
/// operations over `'a`. Serials are creation-ordered (deps-before-uses), so a base
/// op a body references is registered before the recursive op (the same invariant the
/// other registries rely on). The `register_poly_inst_def` close-or-skip guard +
/// kernel `add_decl` re-check keep every registration faithful.
pub(super) fn register_poly_insts(
    theorems: &[IsaProvenTheorem],
    env: &mut Environment,
    registry: &mut PolyInstRegistry,
    methods: &MethodRegistry,
    instance_ops: &InstanceOpRegistry,
    list_fns: &ListFnRegistry,
) {
    let mut order: Vec<usize> = (0..theorems.len()).collect();
    order.sort_by_key(|&i| theorems[i].serial);
    let trace = std::env::var("ISA_TRACE_POLYREG").is_ok();
    // G4 sweep A — the instance overloading LINKS: register every
    // `<impl> → <method>` ALIAS the batch's `…_inst.…` link axioms record
    // (`register_inst_link`; no kernel `Definition` is minted). Swept BEFORE
    // the definition sweep so (a) the (method, instance-shape) ANCHOR set below
    // is complete regardless of the links' serial positions, and (b) a body
    // `_def` whose serial precedes its link still registers.
    for &i in &order {
        if let Some((key, info)) = register_inst_link(&theorems[i], registry, methods) {
            if trace {
                eprintln!(
                    "INSTLINK {} -> {}",
                    key,
                    info.alias_of.as_deref().unwrap_or("?")
                );
            }
            registry.insert(key, info);
        }
    }
    // G4 anchor set: the (method, instance shape) pairs Isabelle's own
    // `instantiation` targets declared — a method-at-constructor body `_def`
    // registers ONLY at one of these (see `register_method_inst_def`).
    let anchors: std::collections::BTreeSet<(String, String)> = registry
        .values()
        .filter_map(|v| v.alias_of.clone().map(|m| (m, isa_shape_key(&v.fn_ty))))
        .collect();
    // Pre-scan: every constant with a recorded `_alt_def` reformulation in the
    // batch declines registration (see `alt_def_head` — registering the head
    // collapses the `_alt_def`'s recorded rewriting chain to a tautology and
    // kernel-rejects a previously-verified node).
    let alt_heads: std::collections::BTreeSet<String> = theorems
        .iter()
        .filter_map(|t| alt_def_head(t).map(str::to_string))
        .collect();
    for &i in &order {
        if let Some((key, def_decl, info)) = register_poly_inst_def_guarded(
            &theorems[i],
            registry,
            methods,
            instance_ops,
            list_fns,
            &alt_heads,
        ) {
            let accepted = env.add_decl(def_decl).is_ok();
            if trace {
                eprintln!(
                    "POLYREG {} tvars={} ops={} accepted={}",
                    key,
                    info.obj_tvars.len(),
                    info.ops.len(),
                    accepted
                );
            }
            if accepted {
                registry.insert(key, info);
            }
        } else if let Some((key, def_decl, info)) = register_method_inst_def(
            &theorems[i],
            registry,
            methods,
            instance_ops,
            list_fns,
            &alt_heads,
            &anchors,
        ) {
            // G4 sweep B — the method-at-constructor instance definitions
            // (composite `(method, shape)` keys; disjoint from the poly-inst
            // lane by construction: `poly_inst_def_axiom` declines overloaded
            // method heads, `method_inst_def_axiom` requires one).
            let accepted = env.add_decl(def_decl).is_ok();
            if trace {
                eprintln!(
                    "INSTKREG {} tvars={} ops={} accepted={}",
                    key.replace('\t', " @ "),
                    info.obj_tvars.len(),
                    info.ops.len(),
                    accepted
                );
            }
            if accepted {
                registry.insert(key, info);
            }
        }
    }
}

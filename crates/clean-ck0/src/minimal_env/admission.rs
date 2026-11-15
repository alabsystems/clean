//! Store only independently admitted records.
use super::*;

impl crate::inductive::MutableEnv for MinimalEnv {
    fn has_inductive(&self, name: &Name) -> bool {
        self.admitted_inductives.contains_key(name)
            || self.admitted_mutuals.contains_key(name)
            || self
                .admission_base
                .as_deref()
                .is_some_and(|base| base.has_inductive(name))
    }

    fn admitted(&self, name: &Name) -> Option<crate::inductive::AdmittedInductive> {
        self.admitted_inductives
            .get(name)
            .cloned()
            .or_else(|| self.admission_base.as_deref()?.admitted(name))
    }

    fn admitted_mutual_decl(&self, name: &Name) -> Option<crate::inductive::InductiveDecl> {
        if let Some(a) = self.admitted_inductives.get(name) {
            return Some(a.decl.clone());
        }
        let Some(m) = self.admitted_mutuals.get(name) else {
            return self.admission_base.as_deref()?.admitted_mutual_decl(name);
        };
        m.block.decls.iter().find(|d| d.name == *name).cloned()
    }

    fn commit_inductive(&mut self, admitted: crate::inductive::AdmittedInductive) {
        let decl = &admitted.decl;
        // Register the inductive type former.
        self.consts.insert(decl.name.clone(), decl.num_level_params);
        self.types.insert(decl.name.clone(), decl.type_.clone());
        self.inductives
            .insert(decl.name.clone(), admitted.large_elim);
        // M3: container metadata so a singly-admitted inductive can later be a
        // nesting container (e.g. List nested inside RoseTree).
        self.ind_num_params
            .insert(decl.name.clone(), decl.num_params);
        self.ind_ctors.insert(
            decl.name.clone(),
            decl.constructors
                .iter()
                .map(|c| (c.name.clone(), c.type_.clone()))
                .collect(),
        );
        // Register constructors (type + param/field arity).
        for ctor in &decl.constructors {
            let arity = crate::inductive::count_pi(&ctor.type_);
            let num_fields = arity.saturating_sub(decl.num_params);
            self.consts.insert(ctor.name.clone(), decl.num_level_params);
            self.types.insert(ctor.name.clone(), ctor.type_.clone());
            self.ctors.insert(
                ctor.name.clone(),
                ConstructorArity {
                    num_params: decl.num_params,
                    num_fields,
                },
            );
        }
        // Single-constructor inductive → also a structure (for proj/structure-η)
        // ONLY when it is a genuine η-structure: 1 ctor, NO indices, NON-recursive
        // (so `mk (proj t) ≡ t`). An indexed or recursive single-ctor inductive
        // (e.g. `Eq`, or a recursive record) is NOT η-eligible — registering it
        // would make structure-η a false-accept. Fail-closed: gate before insert.
        if decl.constructors.len() == 1 {
            let ctor = &decl.constructors[0];
            let arity = crate::inductive::count_pi(&ctor.type_);
            let num_fields = arity.saturating_sub(decl.num_params);
            if crate::inductive::is_eta_structure(
                &ctor.type_,
                decl.num_params,
                admitted.recursor.num_indices,
                decl.constructors.len(),
                std::slice::from_ref(&decl.name),
            ) {
                self.structs.insert(
                    decl.name.clone(),
                    StructureInfo {
                        ctor: ctor.name.clone(),
                        num_params: decl.num_params,
                        num_fields,
                    },
                );
            }
        }
        // Register the recursor: name → inductive map, level-param count, and
        // mark it as a recursor.
        let rec = &admitted.recursor;
        self.consts.insert(rec.name.clone(), rec.num_level_params);
        self.recursors.insert(rec.name.clone());
        self.rec_name_to_ind
            .insert(rec.name.clone(), decl.name.clone());
        self.admitted_inductives.insert(decl.name.clone(), admitted);
    }
}

impl crate::mutual::MutableMutualEnv for MinimalEnv {
    fn commit_mutual(&mut self, admitted: crate::mutual::AdmittedMutual) {
        let np = admitted.block.num_params();
        let nlp = admitted.block.num_level_params();
        // Lean shares the recursion flag across the whole block: every member
        // is excluded from eta if any constructor binder domain mentions a
        // block member, even when that particular member has no fields.
        let family: Vec<Name> = admitted
            .block
            .decls
            .iter()
            .map(|d| d.name.clone())
            .collect();
        // Recursion is a shared property of the entire mutual block in Lean.
        let recursive = admitted.block.decls.iter().any(|d| {
            d.constructors
                .iter()
                .any(|c| crate::inductive::constructor_mentions_family(&c.type_, &family))
        });
        // Register every block type former + constructors + container metadata.
        for d in &admitted.block.decls {
            self.consts.insert(d.name.clone(), nlp);
            self.types.insert(d.name.clone(), d.type_.clone());
            self.inductives.insert(d.name.clone(), admitted.large_elim);
            self.ind_num_params.insert(d.name.clone(), np);
            self.ind_ctors.insert(
                d.name.clone(),
                d.constructors
                    .iter()
                    .map(|c| (c.name.clone(), c.type_.clone()))
                    .collect(),
            );
            for ctor in &d.constructors {
                let arity = crate::inductive::count_pi(&ctor.type_);
                let num_fields = arity.saturating_sub(np);
                self.consts.insert(ctor.name.clone(), nlp);
                self.types.insert(ctor.name.clone(), ctor.type_.clone());
                self.ctors.insert(
                    ctor.name.clone(),
                    ConstructorArity {
                        num_params: np,
                        num_fields,
                    },
                );
            }
            // η-structure gate (mutual): 1 ctor, NO indices, NON-recursive across
            // the whole block. `num_indices` comes from this member's derived
            // recursor; a missing recursor (should not happen) fails the gate.
            if !recursive && d.constructors.len() == 1 {
                let ctor = &d.constructors[0];
                let arity = crate::inductive::count_pi(&ctor.type_);
                let num_fields = arity.saturating_sub(np);
                let num_indices = admitted
                    .recursors
                    .iter()
                    .find(|r| r.inductive == d.name)
                    .map_or(u32::MAX, |r| r.num_indices);
                if crate::inductive::is_eta_structure(
                    &ctor.type_,
                    np,
                    num_indices,
                    d.constructors.len(),
                    &family,
                ) {
                    self.structs.insert(
                        d.name.clone(),
                        StructureInfo {
                            ctor: ctor.name.clone(),
                            num_params: np,
                            num_fields,
                        },
                    );
                }
            }
        }
        // Register each derived recursor: name → inductive map, level count.
        for rec in &admitted.recursors {
            self.consts.insert(rec.name.clone(), rec.num_level_params);
            self.recursors.insert(rec.name.clone());
            self.rec_name_to_ind
                .insert(rec.name.clone(), rec.inductive.clone());
        }
        // Share one immutable block record across all member keys.
        let admitted = std::sync::Arc::new(admitted);
        for d in &admitted.block.decls {
            self.admitted_mutuals
                .insert(d.name.clone(), admitted.clone());
        }
    }
}

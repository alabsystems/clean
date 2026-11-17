//! Temporary admission overlays share the immutable prior environment. Flatten
//! on either outcome, so untrusted inputs cannot accumulate a recursive chain.
use super::*;
impl MinimalEnv {
    // Export-only tightening for the raw shared recursion flag. Checked
    // identity annotations may erase a syntactic family occurrence. Owners
    // are fresh in this transaction, so no inherited structure is masked.
    pub(crate) fn disable_export_structure_eta(&mut self, owners: &[Name]) {
        for name in owners {
            self.structs.remove(name);
        }
    }

    pub(crate) fn begin_export_admission(&mut self) -> bool {
        if self.admission_base.is_some() {
            return false;
        }
        let base = std::sync::Arc::new(std::mem::take(self));
        self.native_nat_folds = base.native_nat_folds.clone();
        self.string_literal_view = base.string_literal_view;
        self.admission_base = Some(base);
        true
    }
    pub(crate) fn end_export_admission(&mut self, checked: Option<Self>) {
        let mut overlay = std::mem::take(self);
        let Some(base) = overlay.admission_base.take() else {
            *self = overlay;
            return;
        };
        let checked = checked.map(|mut delta| {
            // Release the checked overlay's shared base before recovering it.
            delta.admission_base = None;
            delta
        });
        drop(overlay);
        // The reader owns the only remaining reference. The fallback is still
        // infallible if a future caller retains another read-only view.
        *self = match std::sync::Arc::try_unwrap(base) {
            Ok(base) => base,
            Err(shared) => (*shared).clone(),
        };
        if let Some(delta) = checked {
            self.merge_delta(delta);
        }
    }
    fn merge_delta(&mut self, delta: Self) {
        self.consts.extend(delta.consts);
        self.export_hidden.extend(delta.export_hidden);
        self.types.extend(delta.types);
        self.defs.extend(delta.defs);
        self.delta_priorities.extend(delta.delta_priorities);
        self.inductives.extend(delta.inductives);
        self.quots.extend(delta.quots);
        self.recursors.extend(delta.recursors);
        self.ctors.extend(delta.ctors);
        self.structs.extend(delta.structs);
        self.admitted_inductives.extend(delta.admitted_inductives);
        self.rec_name_to_ind.extend(delta.rec_name_to_ind);
        self.ind_num_params.extend(delta.ind_num_params);
        self.ind_ctors.extend(delta.ind_ctors);
        self.admitted_mutuals.extend(delta.admitted_mutuals);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn staging_clones_share_prior_maps_and_flatten_on_both_outcomes() {
        let prior = Name::from_dotted("prior");
        let fresh = Name::from_dotted("fresh");
        let mut env = MinimalEnv::new().with_const(prior.clone(), 0);
        assert!(env.begin_export_admission());
        assert!(env.consts.is_empty());
        let copy = env.clone();
        assert!(std::sync::Arc::ptr_eq(
            env.admission_base.as_ref().unwrap(),
            copy.admission_base.as_ref().unwrap()
        ));
        assert_eq!(copy.num_level_params(&prior), Some(0));
        drop(copy);
        let checked = env.clone().with_const(fresh.clone(), 0);
        env.end_export_admission(Some(checked));
        assert!(env.admission_base.is_none());
        assert_eq!(env.num_level_params(&prior), Some(0));
        assert_eq!(env.num_level_params(&fresh), Some(0));
        assert!(env.begin_export_admission());
        env.end_export_admission(None);
        assert!(env.admission_base.is_none());
        assert_eq!(env.num_level_params(&prior), Some(0));
        assert_eq!(env.num_level_params(&fresh), Some(0));
    }
}

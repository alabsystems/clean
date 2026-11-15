// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{NativeVerificationBundle, NativeVerificationBundleError};

/// The canonical native-bundle admission check over one immutably borrowed input.
///
/// Construction runs [`NativeVerificationBundle::validate`] in full. The private
/// field and shared borrow prevent safe callers from replacing or changing any
/// of its module, contracts, requests, lineage, or input evidence while this fact
/// is reused. A filtered or otherwise changed bundle needs its own admission.
///
/// This is not a solver verdict or source-generation authority. Consumers must
/// still enforce their semantic fragment, select the exact request, honor live
/// deadlines/cancellation, and independently replay output certificates. It also
/// does not establish `trust-ir-build`'s separate module semantic validation.
/// The view is deliberately neither serializable nor constructible from a
/// producer-supplied digest or status.
#[derive(Debug)]
pub struct ValidatedNativeBundle<'a> {
    bundle: &'a NativeVerificationBundle,
}

impl<'a> ValidatedNativeBundle<'a> {
    pub fn new(
        bundle: &'a NativeVerificationBundle,
    ) -> Result<Self, Vec<NativeVerificationBundleError>> {
        bundle.validate()?;
        Ok(Self { bundle })
    }

    /// The exact input that passed the canonical admission check.
    pub fn bundle(&self) -> &'a NativeVerificationBundle {
        self.bundle
    }
}

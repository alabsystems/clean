// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sorry term tracking infrastructure.

mod accounting;
mod build;
mod kind;
mod locations;

pub use accounting::{
    assert_no_sorry, ay_lifetime_count, ay_proof_count, ay_reconstruction_failure_count,
    ay_reconstruction_success_count, deny_sorry_enabled, explicit_sorry_count,
    local_ay_reconstruction_success_count, record_ay_reconstruction_failure,
    record_ay_reconstruction_success, reset_ay_counter, reset_ay_reconstruction_failure_counter,
    reset_ay_reconstruction_success_counter, reset_local_ay_reconstruction_success_counter,
    reset_sorry_counter, sorry_count, sorry_lifetime_count, synthetic_sorry_count,
};
pub use build::{
    create_sorry_term, create_sorry_term_with_kind, create_sorry_term_with_kind_at_level,
    create_trusted_ay_term,
};
pub use kind::SorryKind;
pub use locations::{
    ay_locations, enable_ay_location_tracking, enable_sorry_location_tracking,
    reset_sorry_locations, sorry_locations, with_sorry_location_key,
};

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_location_key;

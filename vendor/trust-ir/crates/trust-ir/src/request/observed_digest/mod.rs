// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Fallible traversal of the actual canonical native-bundle digest preimages.
//! These are identity bytes, never validation or source/proof authority.

use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};

type Result<T = ()> = core::result::Result<T, ObservedValueError>;

mod sink;
use sink::{Writer, digest};
mod ordering;
use ordering::*;

mod fields_0;
use fields_0::*;

mod fields_1;
use fields_1::*;

mod fields_2;
use fields_2::*;

mod fields_3;
use fields_3::*;

mod types;
use types::*;
mod constants;
use constants::*;
mod collections;
use collections::*;
mod tool_name;
use tool_name::*;
mod evidence;
mod identities;

#[cfg(test)]
mod tests;

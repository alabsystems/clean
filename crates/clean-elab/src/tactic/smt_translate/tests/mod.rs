// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

pub(crate) use super::*;
pub(crate) use clean_kernel::name::Name;
pub(crate) use clean_kernel::Level;

mod support;
pub(crate) use support::{make_hdiv, make_hmod, make_hsub, real_of_nat};

mod arithmetic;
mod exists;
mod fallback;
mod fvar_apps;
mod logic;
mod mdata_nat_type_args;
mod parity_gaps;
mod real_constructors;
mod real_div;
mod smoke;
mod typeclass_nat;
mod vars;

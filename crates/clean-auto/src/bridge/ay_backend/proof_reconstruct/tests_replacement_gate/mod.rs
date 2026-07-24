// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-producing replacement gate evidence packet for #2386.
//!
//! Answers whether the ay proof-capable lane can produce a complete proof
//! that clean accepts as a zero-trust kernel refutation for the retained
//! QF_BOOL, QF_UF, and QF_LIA contradiction packet.
//!
//! This is an observability/evidence harness — it does NOT change production
//! routing or widen trust policy. The status matrix surfaces which retained
//! #2386 fragments are replacement-ready and which remain blocked.
//!
//! Part of #2700.

mod cases;
mod snapshot;
mod support;

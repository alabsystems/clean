// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch for `mathverse isabelle-fetch`: load the pinned public-inputs
//! manifest (the built-in copy of `data/isabelle_public_inputs.json`, or
//! `--manifest`), then fetch and check every selected input with the real
//! [`SystemFetcher`] (which shells out to `curl` and `git`).

use super::{IsabelleFetchArgs, MathverseCliError};
use crate::hol::isabelle_fetch::{
    run_fetch, FetchError, FetchOptions, Mode, PublicInputs, SystemFetcher,
};
use crate::hol::isabelle_sessions::expand_tilde;

pub(super) fn cmd_isabelle_fetch(args: IsabelleFetchArgs) -> Result<(), MathverseCliError> {
    run(args).map_err(|e| MathverseCliError::IsabelleFetch(e.to_string()))
}

fn run(args: IsabelleFetchArgs) -> Result<(), FetchError> {
    let inputs = match &args.manifest {
        Some(path) => PublicInputs::load(&expand_tilde(path))?,
        None => PublicInputs::embedded()?,
    };
    let opts = FetchOptions {
        work_dir: expand_tilde(&args.work_dir),
        only: args.only,
        mode: if args.dry { Mode::Dry } else { Mode::Fetch },
    };
    let fetcher = SystemFetcher::for_stderr();
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    run_fetch(&inputs, &opts, &fetcher, &mut out)?.into_result()
}

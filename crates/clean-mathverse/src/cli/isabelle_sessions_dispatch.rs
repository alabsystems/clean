// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch for `mathverse isabelle-sessions` — checkpointed session-ROOT
//! fragment generation for the AFP capture waves (Rust port of the retired
//! `scripts/isabelle/afp_session_gen.py`; same modes, flags, outputs, and
//! stderr summary shapes).

use std::ffi::OsStr;
use std::path::{Path, PathBuf};

use super::{IsabelleSessionsArgs, IsabelleSessionsMode, MathverseCliError};
use crate::hol::isabelle_sessions::afp::{plan_afp_wave, write_afp_wave};
use crate::hol::isabelle_sessions::spine::{plan_spine, write_spine};
use crate::hol::isabelle_sessions::wavec::{plan_wavec, write_wavec};
use crate::hol::isabelle_sessions::{expand_tilde, py_repr, read_entries_file};

pub(super) fn cmd_isabelle_sessions(args: IsabelleSessionsArgs) -> Result<(), MathverseCliError> {
    let out = expand_tilde(&args.out);
    match args.mode {
        IsabelleSessionsMode::Spine => cmd_spine(&args, &out),
        IsabelleSessionsMode::Wavec => cmd_wavec(&args, &out),
        IsabelleSessionsMode::Afp => cmd_afp(&args, &out),
    }
}

fn cmd_spine(args: &IsabelleSessionsArgs, out: &Path) -> Result<(), MathverseCliError> {
    let isabelle_home = std::env::var_os("ISABELLE_HOME");
    let hol_src = resolve_hol_src(args.hol_src.as_deref(), isabelle_home.as_deref())?;
    let plan = plan_spine(&hol_src, args.cap)?;
    for warning in &plan.warnings {
        eprintln!("{warning}");
    }
    write_spine(&plan, out)?;
    eprintln!(
        "emitted {} spine sessions -> {}\n  theories total: {}  cap: {}\n  spine heaps: {}\n  manifest.tsv / sessions.txt / prefixes.txt / spine_heaps.tsv written",
        plan.order.len(),
        out.display(),
        plan.theories_total(),
        args.cap,
        py_dict_repr(&plan.spine_last),
    );
    Ok(())
}

fn resolve_hol_src(
    configured: Option<&Path>,
    isabelle_home: Option<&OsStr>,
) -> Result<PathBuf, crate::hol::isabelle_sessions::IsabelleSessionsError> {
    if let Some(path) = configured {
        return Ok(expand_tilde(path));
    }
    if let Some(home) = isabelle_home.filter(|value| !value.is_empty()) {
        return Ok(expand_tilde(Path::new(home)).join("src/HOL"));
    }
    Err(crate::hol::isabelle_sessions::IsabelleSessionsError::MissingHolSource)
}

fn cmd_wavec(args: &IsabelleSessionsArgs, out: &Path) -> Result<(), MathverseCliError> {
    let entries = read_entries(args)?;
    let afp_thys = expand_tilde(&args.afp_thys);
    let plan = plan_wavec(&afp_thys, &entries)?;
    write_wavec(&plan, out)?;
    eprintln!(
        "wave-C DAG: seed(math)={} closure={} (+{} provider entries) unresolved-roots={} -> {}",
        plan.seed_count,
        plan.rows.len(),
        plan.rows.len() as i64 - plan.seed_count as i64,
        plan.unresolved().len(),
        out.join("afp_wave_c_dag.tsv").display(),
    );
    Ok(())
}

fn cmd_afp(args: &IsabelleSessionsArgs, out: &Path) -> Result<(), MathverseCliError> {
    let entries = read_entries(args)?;
    let afp_thys = expand_tilde(&args.afp_thys);
    let plan = plan_afp_wave(&entries, &afp_thys, &args.parent, args.cap)?;
    for warning in &plan.warnings {
        eprintln!("{warning}");
    }
    write_afp_wave(&plan, out)?;
    eprintln!(
        "emitted {} sessions ({} entries requested) -> {}\n  theories total: {}  parent heap: {}  cap: {}\n  manifest.tsv / sessions.txt / prefixes.txt written",
        plan.order.len(),
        plan.entries_requested,
        out.display(),
        plan.theories_total(),
        args.parent,
        args.cap,
    );
    Ok(())
}

fn read_entries(args: &IsabelleSessionsArgs) -> Result<Vec<String>, MathverseCliError> {
    match &args.entries {
        Some(path) => Ok(read_entries_file(&expand_tilde(path))?),
        None => Ok(Vec::new()),
    }
}

/// Python `dict` repr of the spine→last-chunk map, matching the original
/// script's `spine heaps: {…}` stderr line.
fn py_dict_repr(pairs: &[(String, String)]) -> String {
    let body = pairs
        .iter()
        .map(|(k, v)| format!("{}: {}", py_repr(k), py_repr(v)))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{{{body}}}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_py_dict_repr_matches_python_shape() {
        assert_eq!(py_dict_repr(&[]), "{}");
        assert_eq!(
            py_dict_repr(&[
                ("HOL-Analysis".to_string(), "ZP-Analysis-9".to_string()),
                ("HOL-Algebra".to_string(), "ZP-Algebra".to_string()),
            ]),
            "{'HOL-Analysis': 'ZP-Analysis-9', 'HOL-Algebra': 'ZP-Algebra'}"
        );
    }

    #[test]
    fn hol_source_prefers_explicit_path_then_isabelle_home() {
        assert_eq!(
            resolve_hol_src(Some(Path::new("/explicit/HOL")), Some(OsStr::new("/env"))).unwrap(),
            PathBuf::from("/explicit/HOL")
        );
        assert_eq!(
            resolve_hol_src(None, Some(OsStr::new("/opt/Isabelle"))).unwrap(),
            PathBuf::from("/opt/Isabelle/src/HOL")
        );
    }

    #[test]
    fn hol_source_without_flag_or_environment_fails_closed() {
        assert!(matches!(
            resolve_hol_src(None, None),
            Err(crate::hol::isabelle_sessions::IsabelleSessionsError::MissingHolSource)
        ));
        assert!(matches!(
            resolve_hol_src(None, Some(OsStr::new(""))),
            Err(crate::hol::isabelle_sessions::IsabelleSessionsError::MissingHolSource)
        ));
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Optional native execution and admission signatures, never logical foundations.
//! These axioms were the last twenty value-less non-foundations in the default
//! prelude. The untrusted source elaborator may request them; the kernel never
//! invents a missing constant, and registration still checks every declaration.

use super::{EnvError, Environment};
use crate::name::Name;
use std::collections::BTreeSet;

const IO_NAMES: [&str; 15] = [
    "IO",
    "IO.pure",
    "IO.bind",
    "instMonadIO",
    "IO.println",
    "IO.print",
    "IO.eprintln",
    "IO.getLine",
    "IO.FS.readFile",
    "IO.FS.writeFile",
    "IO.getEnv",
    "IO.currentDir",
    "IO.Process.exit",
    "IO.monoMsNow",
    "IO.panic",
];
const CONTROL_NAMES: [&str; 2] = ["tryCatchThe", "tryFinally"];
const ADMISSION_NAMES: [&str; 4] = ["sorry", "sorryAx", "trustedArith", "trustedAy"];
/// The source options that bound a checker's resources (`checker_settings`).
const FIXED_FRAGMENT_RESOURCE_OPTIONS: [&str; 2] = ["maxHeartbeats", "tcMaxCacheEntries"];

pub(super) fn is_bootstrap_stub_name(name: &Name) -> bool {
    IO_NAMES
        .iter()
        .chain(&CONTROL_NAMES)
        .chain(&ADMISSION_NAMES)
        .any(|text| *name == Name::from_string(text))
}

impl Environment {
    /// Opt in to the old native IO vocabulary. Every signature stays an axiom;
    /// runtime support is not a proof. Genuine imported IO is never replaced.
    ///
    /// # Errors
    /// Propagates checked IO registration errors.
    pub fn init_io_stub_theory(&mut self) -> Result<(), EnvError> {
        if self.suppresses_lossy_structure_stubs()
            || (self.get_const(&Name::from_string("IO")).is_some() && !self.has_io())
        {
            return Ok(());
        }
        self.init_io_ops()
    }

    /// Opt in to admission markers. Their axiom closures remain explicit, and
    /// the reference entry and default CLI admission policy still refuse them.
    ///
    /// # Errors
    /// Propagates checked marker or Bool registration errors.
    pub fn init_admission_stub_theory(&mut self) -> Result<(), EnvError> {
        self.init_sorry()?;
        self.init_trusted_arith()?;
        self.init_trusted_ay()?;
        self.init_bool()?;
        self.init_sorry_ax()
    }

    /// An isolated context for the untrusted elaborator's bootstrap vocabulary.
    /// Never install this context as the checked registration environment.
    /// Bare-source worlds get no substitute symbols; import worlds get no
    /// native IO/control substitutes for genuine checked Lean declarations.
    ///
    /// # Errors
    /// Propagates checked optional-fragment registration errors.
    pub fn bootstrap_stub_advice(&self) -> Result<Self, EnvError> {
        let mut advice = self.clone();
        if self.models_lean_init() {
            advice.with_fixed_fragment_resources(|advice| {
                advice.init_admission_stub_theory()?;
                if !advice.suppresses_lossy_structure_stubs() {
                    advice.init_io_stub_theory()?;
                    advice.init_control_stub_theory()?;
                }
                Ok(())
            })?;
        }
        Ok(advice)
    }

    /// Register a fixed fragment with the checker's default resource bounds.
    /// A source `set_option maxHeartbeats`/`tcMaxCacheEntries` bounds the
    /// user's own declarations, which keep it; these signatures are fixed and
    /// still fully kernel-checked, and before bcacce6e0 they sat in the
    /// prelude, outside every source option's scope.
    fn with_fixed_fragment_resources(
        &mut self,
        register: impl FnOnce(&mut Self) -> Result<(), EnvError>,
    ) -> Result<(), EnvError> {
        let saved: Vec<(&str, Option<String>)> = FIXED_FRAGMENT_RESOURCE_OPTIONS
            .iter()
            .filter_map(|key| {
                let value = self.get_option(key).cloned()?;
                self.remove_option(key);
                Some((*key, value))
            })
            .collect();
        let result = register(self);
        for (key, value) in saved {
            self.set_option(key.to_string(), value);
        }
        result
    }

    fn missing_bootstrap_fragment(&self, roots: &BTreeSet<Name>, names: &[&str]) -> bool {
        self.models_lean_init()
            && names.iter().any(|text| {
                let name = Name::from_string(text);
                roots.contains(&name) && self.get_const(&name).is_none()
            })
    }

    /// Whether exact structural kernel references request an absent fragment.
    /// String literals, comments, and printed-name collisions cannot opt in.
    pub fn needs_bootstrap_stubs(&self, roots: &BTreeSet<Name>) -> bool {
        self.missing_bootstrap_fragment(roots, &ADMISSION_NAMES)
            || (!self.suppresses_lossy_structure_stubs()
                && (self.missing_bootstrap_fragment(roots, &IO_NAMES)
                    || self.missing_bootstrap_fragment(roots, &CONTROL_NAMES)))
    }

    /// Explicit frontend opt-in, before the ordinary full kernel check. Call
    /// transactionally so a rejected declaration leaves no stub fragments.
    ///
    /// # Errors
    /// Propagates checked requested-fragment registration errors.
    pub fn init_requested_bootstrap_stubs(
        &mut self,
        roots: &BTreeSet<Name>,
    ) -> Result<(), EnvError> {
        let admission = self.missing_bootstrap_fragment(roots, &ADMISSION_NAMES);
        let lossy_allowed = !self.suppresses_lossy_structure_stubs();
        let io = lossy_allowed && self.missing_bootstrap_fragment(roots, &IO_NAMES);
        let control = lossy_allowed && self.missing_bootstrap_fragment(roots, &CONTROL_NAMES);
        self.with_fixed_fragment_resources(|env| {
            if admission {
                env.init_admission_stub_theory()?;
            }
            if io {
                env.init_io_stub_theory()?;
            }
            if control {
                env.init_control_stub_theory()?;
            }
            Ok(())
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ConstantKind;

    #[test]
    fn bootstrap_stubs_are_explicit_and_structural() {
        let mut env = Environment::with_prelude();
        assert!(env.stub_theory_axioms().is_empty());
        let advice = env.bootstrap_stub_advice().expect("untrusted advice");
        assert_eq!(advice.stub_theory_axioms().len(), 20);
        assert!(
            env.stub_theory_axioms().is_empty(),
            "advice never replaces checked context"
        );
        for text in IO_NAMES
            .iter()
            .chain(&CONTROL_NAMES)
            .chain(&ADMISSION_NAMES)
        {
            let canonical = Name::from_string(text);
            assert!(is_bootstrap_stub_name(&canonical));
            if text.contains('.') {
                let masquerade = Name::anon().str(text);
                assert_eq!(masquerade.to_string(), canonical.to_string());
                assert!(!is_bootstrap_stub_name(&masquerade));
                let roots = BTreeSet::from([masquerade]);
                assert!(!env.needs_bootstrap_stubs(&roots));
                env.init_requested_bootstrap_stubs(&roots)
                    .expect("no fragment requested");
                assert!(env.stub_theory_axioms().is_empty());
            }
        }
        let roots = BTreeSet::from([Name::from_string("IO.println")]);
        assert!(env.needs_bootstrap_stubs(&roots));
        env.init_requested_bootstrap_stubs(&roots)
            .expect("IO request");
        assert!(!env.needs_bootstrap_stubs(&roots));
        assert_eq!(env.stub_theory_axioms().len(), 14);
        assert!(env.get_const(&Name::from_string("sorryAx")).is_none());
        assert!(env.get_const(&Name::from_string("tryFinally")).is_none());
        env.init_control_stub_theory().expect("explicit control");
        env.init_admission_stub_theory()
            .expect("explicit admission");
        assert_eq!(env.stub_theory_axioms().len(), 20);
        for name in env.stub_theory_axioms() {
            assert_eq!(
                env.get_const(&name).expect("stub").kind,
                ConstantKind::Axiom
            );
        }
    }

    #[test]
    fn bootstrap_fragments_ignore_and_restore_source_resource_bounds() {
        let mut env = Environment::with_prelude();
        env.set_option("maxHeartbeats".to_string(), Some("1".to_string()));
        env.set_option("tcMaxCacheEntries".to_string(), Some("1".to_string()));
        // Control: the bound is live for an ordinary checked declaration.
        let mut bounded = env.clone();
        bounded
            .init_io_ops()
            .expect_err("maxHeartbeats 1 must refuse a direct IO registration");
        let advice = env
            .bootstrap_stub_advice()
            .expect("advice under a source bound");
        assert_eq!(advice.stub_theory_axioms().len(), 20);
        let roots = BTreeSet::from([Name::from_string("IO.println")]);
        env.init_requested_bootstrap_stubs(&roots)
            .expect("requested IO under a source bound");
        assert_eq!(env.stub_theory_axioms().len(), 14);
        for checked in [&env, &advice] {
            for key in FIXED_FRAGMENT_RESOURCE_OPTIONS {
                assert_eq!(
                    checked.get_option(key),
                    Some(&Some("1".to_string())),
                    "{key} is restored for the source's own declarations"
                );
            }
        }
    }

    #[test]
    fn bootstrap_advice_respects_bare_and_import_worlds() {
        let bare = Environment::default();
        let advice = bare.bootstrap_stub_advice().expect("bare advice");
        assert_eq!(advice.constants().count(), 0);
        let imported = Environment::try_with_prelude_for_import().expect("import prelude");
        assert!(imported.stub_theory_axioms().is_empty());
        let advice = imported.bootstrap_stub_advice().expect("import advice");
        assert_eq!(advice.stub_theory_axioms().len(), 4);
        assert!(advice.get_const(&Name::from_string("IO")).is_none());
        assert!(advice
            .get_const(&Name::from_string("tryCatchThe"))
            .is_none());
    }
}

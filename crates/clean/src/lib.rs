// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean primary Rust interface.
//!
//! This crate re-exports the kernel and .olean loader APIs, plus
//! ergonomic helpers for building expressions and loading standard
//! libraries without JSON-RPC overhead.
//!
//! Certificate APIs are available under `clean::kernel::cert` and are also
//! re-exported as top-level types such as `clean::ProofCert` and `clean::CertVerifier`.
//!
//! # Quick Start
//!
//! Use the prelude for ergonomic imports:
//!
//! ```rust,no_run
//! use clean::prelude::*;
//!
//! // Create an environment with Init library loaded
//! let env = Environment::with_init().expect("Init available");
//!
//! // Or manually load libraries
//! let mut env = Environment::new();
//! let cache = ModuleCache::new();
//! env.load_init(&cache).expect("load Init");
//!
//! // Build a type checker for type inference
//! let tc = env.type_checker();
//! ```
//!
//! The prelude re-exports:
//! - [`EnvironmentExt`] - Extension trait with `load_init()`, `with_init()`, etc.
//! - [`TypeCheckerExt`] - Expression construction helpers
//! - Core kernel types ([`Environment`], [`Expr`], [`TypeChecker`], etc.)
//! - Module loading types ([`ModuleCache`], [`ImportError`], etc.)

pub use clean_kernel as kernel;
pub use clean_olean as olean;
pub use clean_parser as parser;

// Source check pipeline (absorbed from the former `clean-lib` crate;
// rearch stage 9 facade consolidation — `clean` is the ONE Rust facade).
pub mod check;
pub mod parallel;

// Re-export the check pipeline's main entry points and result types at the
// crate root so downstream `cargo test` suites keep a flat import surface.
pub use check::{
    check_file, check_source, load_file_into, load_source_into, CheckConfig, CheckResult,
    DeclResult, DeclWarning,
};

// Re-export commonly used kernel types explicitly for semver safety
// (wildcard re-exports cause breaking changes when clean_kernel adds new public items)
pub use clean_kernel::cert::{
    BuildResult, CertBuilder, CertError, CertVerifier, DefEqStep, NodeId, ProofCert,
};
pub use clean_kernel::{
    // Aesop
    AesopIndexMode,
    AesopRule,
    AesopRuleBuilder,
    AesopRulePhase,
    AesopRuleSet,
    // Mode system
    AxiomId,
    // Batch verification
    BatchCheckResult,
    BatchCheckStats,
    BatchConfig,
    BatchVerifier,
    // Big integer support (for Literal::Nat)
    BigNat,
    // Expression building
    BinderInfo,
    CleanMode,
    // Declarations and environment
    ConstantInfo,
    // Inductives
    Constructor,
    ConstructorVal,
    Declaration,
    EnvError,
    // Core types
    Environment,
    Expr,
    ExprKind,
    FVarId,
    InductiveDecl,
    InductiveError,
    InductiveType,
    InductiveVal,
    KernelClassInfo,
    KernelInstanceInfo,
    Level,
    LevelVec,
    Literal,
    // Type checking
    LocalContext,
    LocalDecl,
    MDataMap,
    MDataValue,
    ModeError,
    Name,
    // Quotient types
    QuotKind,
    QuotVal,
    RecursorArgOrder,
    RecursorRule,
    RecursorVal,
    Reducibility,
    SourceSystem,
    TransparencyMode,
    TypeChecker,
    TypeError,
    VerificationArena,
    DEFAULT_INSTANCE_PRIORITY,
};
pub use clean_olean::{
    default_search_paths, load_module_with_deps, load_module_with_deps_cached,
    load_module_with_deps_parallel, load_olean_file, ImportError, LoadSummary, ModuleCache,
    SkippedConstant,
};

/// Extension helpers for clean kernel environments.
pub trait EnvironmentExt {
    /// Construct a `TypeChecker` for this environment.
    fn type_checker(&self) -> TypeChecker<'_>;

    /// Load a Lean module (and its imports) into this environment using the provided cache.
    ///
    /// Uses [`default_search_paths`] for locating `.olean` files. For custom search paths,
    /// use [`Self::load_module_with_paths`] instead.
    fn load_module_with_cache(
        &mut self,
        module: &str,
        cache: &ModuleCache,
    ) -> Result<Vec<LoadSummary>, ImportError>;

    /// Load a Lean module (and its imports) into this environment using custom search paths.
    ///
    /// This provides flexibility for projects with non-standard `.olean` locations.
    fn load_module_with_paths(
        &mut self,
        module: &str,
        paths: &[std::path::PathBuf],
        cache: &ModuleCache,
    ) -> Result<Vec<LoadSummary>, ImportError>;

    /// Load `Init` and its imports into this environment.
    fn load_init(&mut self, cache: &ModuleCache) -> Result<Vec<LoadSummary>, ImportError>;

    /// Load `Std` and its imports into this environment.
    fn load_std(&mut self, cache: &ModuleCache) -> Result<Vec<LoadSummary>, ImportError>;

    /// Load `Mathlib` and its imports into this environment.
    fn load_mathlib(&mut self, cache: &ModuleCache) -> Result<Vec<LoadSummary>, ImportError>;

    /// Build a new environment with `Init` loaded from `.olean` files.
    fn with_init() -> Result<Environment, ImportError>;

    /// Build a new environment with `Std` loaded from `.olean` files.
    fn with_std() -> Result<Environment, ImportError>;

    /// Build a new environment with `Mathlib` loaded from `.olean` files.
    fn with_mathlib() -> Result<Environment, ImportError>;

    /// Parse and elaborate Lean source into this environment.
    ///
    /// Method-style form of [`check::load_source_into`] (absorbed from the
    /// former `clean-lib` crate):
    ///
    /// ```rust,no_run
    /// use clean::kernel::Environment;
    /// use clean::{CheckConfig, EnvironmentExt};
    ///
    /// let mut env = Environment::try_with_prelude().expect("prelude");
    /// let result = env
    ///     .load_lean_source("def base : Nat := 7", &CheckConfig::default())
    ///     .expect("load should succeed");
    /// assert!(result.errors.is_empty());
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`check::Error::Parse`] if parsing fails.
    fn load_lean_source(
        &mut self,
        source: &str,
        config: &CheckConfig,
    ) -> Result<CheckResult, check::Error>;

    /// Parse and elaborate a Lean source file into this environment.
    ///
    /// Method-style form of [`check::load_file_into`].
    ///
    /// # Errors
    ///
    /// Returns [`check::Error::Io`] if the file cannot be read, or
    /// [`check::Error::Parse`] if parsing fails.
    fn load_lean_file(
        &mut self,
        path: impl AsRef<std::path::Path>,
        config: &CheckConfig,
    ) -> Result<CheckResult, check::Error>;
}

impl EnvironmentExt for Environment {
    fn type_checker(&self) -> TypeChecker<'_> {
        TypeChecker::with_mode(self, self.mode())
    }

    fn load_module_with_cache(
        &mut self,
        module: &str,
        cache: &ModuleCache,
    ) -> Result<Vec<LoadSummary>, ImportError> {
        let paths = default_search_paths();
        load_module_with_deps_cached(self, module, &paths, cache)
    }

    fn load_module_with_paths(
        &mut self,
        module: &str,
        paths: &[std::path::PathBuf],
        cache: &ModuleCache,
    ) -> Result<Vec<LoadSummary>, ImportError> {
        load_module_with_deps_cached(self, module, paths, cache)
    }

    fn load_init(&mut self, cache: &ModuleCache) -> Result<Vec<LoadSummary>, ImportError> {
        self.load_module_with_cache("Init", cache)
    }

    fn load_std(&mut self, cache: &ModuleCache) -> Result<Vec<LoadSummary>, ImportError> {
        self.load_module_with_cache("Std", cache)
    }

    fn load_mathlib(&mut self, cache: &ModuleCache) -> Result<Vec<LoadSummary>, ImportError> {
        self.load_module_with_cache("Mathlib", cache)
    }

    fn with_init() -> Result<Environment, ImportError> {
        let mut env = Environment::new();
        let cache = ModuleCache::new();
        env.load_init(&cache)?;
        Ok(env)
    }

    fn with_std() -> Result<Environment, ImportError> {
        let mut env = Environment::new();
        let cache = ModuleCache::new();
        env.load_std(&cache)?;
        Ok(env)
    }

    fn with_mathlib() -> Result<Environment, ImportError> {
        let mut env = Environment::new();
        let cache = ModuleCache::new();
        env.load_mathlib(&cache)?;
        Ok(env)
    }

    fn load_lean_source(
        &mut self,
        source: &str,
        config: &CheckConfig,
    ) -> Result<CheckResult, check::Error> {
        load_source_into(self, source, config)
    }

    fn load_lean_file(
        &mut self,
        path: impl AsRef<std::path::Path>,
        config: &CheckConfig,
    ) -> Result<CheckResult, check::Error> {
        load_file_into(self, path, config)
    }
}

/// Ergonomic expression construction helpers on top of `Expr`.
pub trait TypeCheckerExt {
    /// Build a constant expression from a string name.
    fn const_(&self, name: impl AsRef<str>) -> Expr;

    /// Build a constant expression with explicit universe levels.
    fn const_levels(&self, name: impl AsRef<str>, levels: impl Into<LevelVec>) -> Expr;

    /// Build an application of `func` to multiple arguments.
    fn app(&self, func: Expr, args: impl IntoIterator<Item = Expr>) -> Expr;

    /// Build a natural number literal expression from a `u64`.
    fn lit(&self, value: u64) -> Expr;

    /// Build a natural number literal expression from a `BigNat`.
    ///
    /// Use this for arbitrarily large natural numbers that exceed `u64::MAX`.
    fn lit_bignat(&self, value: BigNat) -> Expr;

    /// Build a string literal expression.
    fn lit_str(&self, value: impl AsRef<str>) -> Expr;
}

impl TypeCheckerExt for TypeChecker<'_> {
    fn const_(&self, name: impl AsRef<str>) -> Expr {
        Expr::const_str(name.as_ref())
    }

    fn const_levels(&self, name: impl AsRef<str>, levels: impl Into<LevelVec>) -> Expr {
        Expr::const_str_levels(name.as_ref(), levels)
    }

    fn app(&self, func: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
        Expr::apps(func, args)
    }

    fn lit(&self, value: u64) -> Expr {
        Expr::nat_lit(value)
    }

    fn lit_bignat(&self, value: BigNat) -> Expr {
        Expr::from_kind(ExprKind::Lit(Literal::Nat(value)))
    }

    fn lit_str(&self, value: impl AsRef<str>) -> Expr {
        Expr::str_lit(value.as_ref())
    }
}

/// Common imports for Rust API users.
pub mod prelude {
    pub use crate::{EnvironmentExt, TypeCheckerExt};
    pub use clean_kernel::{
        BatchCheckResult, BatchCheckStats, BatchConfig, BatchVerifier, BigNat, BinderInfo,
        Environment, Expr, Level, LevelVec, Literal, Name, TypeChecker, TypeError,
        VerificationArena,
    };
    pub use clean_olean::{
        default_search_paths, ImportError, LoadSummary, ModuleCache, SkippedConstant,
    };
}

#[cfg(test)]
mod tests {
    use super::{EnvironmentExt, TypeCheckerExt};
    use clean_kernel::{Expr, ExprKind, Level, Literal, Name};

    #[test]
    fn type_checker_ext_builds_constants_and_literals() {
        let env = clean_kernel::Environment::new();
        let tc = env.type_checker();

        let nat = tc.const_("Nat");
        assert!(matches!(
            nat.kind(),
            ExprKind::Const(name, levels)
                if *name == Name::from_string("Nat") && levels.is_empty()
        ));

        let list = tc.const_levels("List", vec![Level::zero()]);
        assert!(matches!(
            list.kind(),
            ExprKind::Const(name, levels)
                if *name == Name::from_string("List") && levels.as_slice() == [Level::zero()]
        ));

        let lit = tc.lit(42);
        assert_eq!(
            lit,
            Expr::from_kind(ExprKind::Lit(Literal::Nat(clean_kernel::BigNat::Small(42))))
        );

        // Test lit_bignat with Small variant
        let big_small = tc.lit_bignat(clean_kernel::BigNat::Small(123));
        assert_eq!(
            big_small,
            Expr::from_kind(ExprKind::Lit(Literal::Nat(clean_kernel::BigNat::Small(
                123
            ))))
        );

        // Test lit_bignat with Big variant
        let big_big = tc.lit_bignat(clean_kernel::BigNat::Big(vec![1, 2]));
        assert_eq!(
            big_big,
            Expr::from_kind(ExprKind::Lit(Literal::Nat(clean_kernel::BigNat::Big(
                vec![1, 2]
            ))))
        );

        let lit_str = tc.lit_str("clean");
        assert_eq!(
            lit_str,
            Expr::from_kind(ExprKind::Lit(Literal::String("clean".into())))
        );
    }

    #[test]
    fn type_checker_ext_builds_apps() {
        let env = clean_kernel::Environment::new();
        let tc = env.type_checker();

        let func = tc.const_("f");
        let arg_a = tc.const_("a");
        let arg_b = tc.const_("b");
        let app = tc.app(func.clone(), vec![arg_a.clone(), arg_b.clone()]);

        let expected = Expr::app(Expr::app(func, arg_a), arg_b);
        assert_eq!(app, expected);
    }
}

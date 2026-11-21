// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Install supported exported grammar before parsing an artifact-only file.

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::sync::Arc;

use clean_kernel::{Environment, Expr, LeanWorld, Name};
use clean_olean::import::runtime::RuntimeExtractionLimits;
use clean_olean::{
    load_modules_with_term_providers, ExportedNumeralSyntax, ExportedTermProviders,
    ModuleCaptureLimits, OleanImportError,
};
use clean_parser::{
    FileHeader, ImportedTermPrefixError, ImportedTermPrefixes, Span, SurfaceArg, SurfaceExpr,
    SurfaceLit,
};

use crate::{ElabError, FileContext};

use super::imported_runtime::ImportedRuntime;

struct Handler {
    declaration: Name,
    bytes: Arc<[u8]>,
    providers: Arc<ExportedTermProviders>,
}

pub(crate) struct ImportedTermSyntax {
    source: Arc<str>,
    handlers: HashMap<Name, Handler>,
}

impl ImportedTermSyntax {
    pub(crate) fn elaborate(
        &self,
        env: &Environment,
        kind: &Name,
        head: Span,
        args: &[SurfaceArg],
    ) -> Result<Expr, ElabError> {
        let handler = self.handlers.get(kind).ok_or_else(|| {
            ElabError::NotImplemented(format!(
                "no exported term elaborator is available for `{kind}`"
            ))
        })?;
        let [arg] = args else {
            return Err(ElabError::NotImplemented(format!(
                "exported term elaborator `{}` requires a single numeral argument",
                handler.declaration
            )));
        };
        if arg.name.is_some() {
            return Err(ElabError::NotImplemented(
                "imported numeral syntax does not accept a named argument".to_owned(),
            ));
        }
        let SurfaceExpr::Lit(numeral, SurfaceLit::Nat(_) | SurfaceLit::BigNat(_)) = &arg.expr
        else {
            return Err(ElabError::NotImplemented(format!(
                "exported term elaborator `{}` expects a numeral",
                handler.declaration
            )));
        };
        let (Some(token), Some(numeral)) = (
            self.source.get(head.start..head.end),
            self.source.get(numeral.start..numeral.end),
        ) else {
            return Err(ElabError::NotImplemented(
                "imported term syntax has an invalid source span".to_owned(),
            ));
        };
        handler
            .providers
            .evaluate(
                env,
                &handler.bytes,
                &handler.declaration,
                ExportedNumeralSyntax {
                    kind,
                    token,
                    numeral,
                },
            )
            .map_err(|error| {
                ElabError::NotImplemented(format!(
                    "exported term elaborator `{}`: {error}",
                    handler.declaration
                ))
            })
    }
}

/// Start an ordinary stable artifact-only module and gather its exported
/// syntax, checking its implicit Init and explicit roots in a single graph.
/// Prelude files use their empty environment and ordinary ordered imports.
///
/// # Errors
/// Refuses an incompatible file header or source world, missing or invalid
/// artifacts, and the same parser/runtime conflicts as the explicit loader.
pub fn stable_environment_with_imported_syntax(
    decision: &clean_olean::SourceWorldDecision,
    header: &FileHeader,
    paths: Vec<PathBuf>,
    main_module: Name,
    source: &str,
    native_main: bool,
) -> Result<(Environment, FileContext, ImportedTermPrefixes), ElabError> {
    if decision.world() != LeanWorld::Lean436 || header.is_prelude {
        return Err(ElabError::SourceWorld(
            "combined imports require an ordinary stable module".into(),
        ));
    }
    decision
        .imports()
        .map_err(|error| ElabError::SourceWorld(error.to_string()))?;
    let mut env =
        super::setup::genuine_replay_environment(super::EnvironmentSetup::default(), decision)?;
    let mut context = FileContext::new();
    context.set_artifact_source_world(decision, paths);
    context.set_main_module(main_module);
    context.set_file_header(header);
    let init = Name::from_string("Init");
    context.record_compiler_import(&init);
    let prefixes = preload_imports(
        &mut env,
        &mut context,
        header,
        source,
        native_main,
        Some(&init),
    )?;
    Ok((env, context, prefixes))
}

/// Load the explicit header imports of an ordinary stable Lean file and collect
/// visible global parser registrations from the same artifact bytes.
///
/// The caller parses the body with the returned prefixes and marks the header
/// imports as preloaded. Named scopes and arbitrary parser descriptors require
/// their own grammar support. A native invocation also retains the compiled
/// parts of its direct runtime imports.
///
/// # Errors
/// Refuses an incompatible context, import, or conflicting supported parser.
pub fn preload_exported_term_syntax(
    env: &mut Environment,
    context: &mut FileContext,
    header: &FileHeader,
    source: &str,
    native_main: bool,
) -> Result<ImportedTermPrefixes, ElabError> {
    preload_imports(env, context, header, source, native_main, None)
}

fn preload_imports(
    env: &mut Environment,
    context: &mut FileContext,
    header: &FileHeader,
    source: &str,
    native_main: bool,
    bootstrap: Option<&Name>,
) -> Result<ImportedTermPrefixes, ElabError> {
    let fail = |reason| ElabError::UnresolvedImport {
        module: header
            .imports
            .first()
            .map(|import| import.module.name().to_string())
            .unwrap_or_default(),
        reason,
    };
    let world = context
        .lean_world()
        .map_err(|error| ElabError::SourceWorld(error.to_string()))?;
    if world != LeanWorld::Lean436
        || !context.imports_require_artifacts()
        || (header.is_prelude
            && (!native_main
                || !crate::source_prelude::is_bare_module(env)
                || env.num_constants() != 0))
    {
        return Err(fail(
            "exported term syntax requires a stable artifact context with a fresh explicit prelude"
                .to_owned(),
        ));
    }
    let roots: Vec<_> = header
        .imports
        .iter()
        .map(|import| (import.module.name().clone(), import.import_all))
        .collect();
    let mut prefixes = ImportedTermPrefixes::default();
    let capture_bootstrap_runtime = native_main && bootstrap.is_some();
    if roots.is_empty() && !capture_bootstrap_runtime {
        context.imported_term_syntax = None;
        context.imported_runtime = None;
        return Ok(prefixes);
    }
    let paths = context
        .effective_import_search_paths()
        .map_err(|error| fail(error.to_string()))?;
    let direct: HashSet<_> = roots.iter().map(|(name, _)| name.clone()).collect();
    let compiled: HashSet<_> = header
        .imports
        .iter()
        .filter(|import| !header.is_module || import.import_all || import.is_meta)
        .map(|import| import.module.name().clone())
        .collect();
    let native_imports: HashSet<_> = header
        .imports
        .iter()
        .filter(|import| native_main && (!header.is_module || import.import_all || !import.is_meta))
        .map(|import| import.module.name().clone())
        .collect();
    let mut handlers = HashMap::<Name, Handler>::new();
    let mut runtime = ImportedRuntime::default();
    let mut char_program = native_main.then(clean_olean::StableCharProgramCheck::default);
    let mut nat_dictionary = native_main.then(clean_olean::StableNatDictionaryCheck::default);
    let mut stdout_inputs = (capture_bootstrap_runtime
        || (native_main && header.imports.iter().any(|i| !i.is_meta)))
    .then(clean_olean::StableStdoutImportCheck::default);
    let mut io_error_inputs = (native_main
        && header.is_prelude
        && !header.is_module
        && header
            .imports
            .iter()
            .any(|i| !i.is_meta && i.module.name() == &Name::interned("Init.System.IO")))
    .then(clean_olean::StableIoErrorImportCheck::default);
    load_modules_with_term_providers(
        env,
        bootstrap,
        capture_bootstrap_runtime,
        &roots,
        header.is_module,
        &paths,
        ModuleCaptureLimits::new(
            RuntimeExtractionLimits::default().max_part_bytes,
            usize::MAX,
            crate::imports::FRONTEND_OLEAN_IMPORT_MODULE_LIMIT,
            usize::MAX,
        ),
        &mut |module, _, capture| {
            let private = clean_olean::CapturedPrivateNativeModule::new(module, capture);
            if let Some(check) = &mut char_program {
                check.observe(&private);
            }
            if let Some(check) = &mut nat_dictionary {
                check.observe(&private);
            }
            if let Some(check) = &mut stdout_inputs {
                check.observe(&private);
            }
            if let Some(check) = &mut io_error_inputs {
                check.observe_module(&private);
            }
            if direct.contains(module) {
                runtime.insert(
                    module,
                    Arc::from(capture.base),
                    capture,
                    compiled.contains(module),
                    native_imports.contains(module),
                    header.is_module,
                );
            }
            Ok(())
        },
        &mut |module, base, descriptors, providers| {
            let bytes = Arc::<[u8]>::from(base);
            for descriptor in descriptors {
                let Ok(precedence) = u32::try_from(descriptor.precedence) else {
                    continue;
                };
                match prefixes.register_numeral_prefix(
                    descriptor.kind.clone(),
                    precedence,
                    &descriptor.literal,
                ) {
                    Ok(()) => {}
                    Err(
                        ImportedTermPrefixError::UnsupportedLiteral(_)
                        | ImportedTermPrefixError::UnsupportedPrecedence(_),
                    ) => continue,
                    Err(error) => {
                        return Err(OleanImportError::UnsupportedModule {
                            module: module.to_string(),
                            reason: error.to_string(),
                        })
                    }
                }
                if let Some(existing) = handlers.get(&descriptor.kind) {
                    if existing.declaration != descriptor.handler || existing.bytes != bytes {
                        return Err(OleanImportError::UnsupportedModule {
                            module: module.to_string(),
                            reason: format!("ambiguous term elaborator for `{}`", descriptor.kind),
                        });
                    }
                } else {
                    handlers.insert(
                        descriptor.kind,
                        Handler {
                            declaration: descriptor.handler,
                            bytes: Arc::clone(&bytes),
                            providers: Arc::clone(&providers),
                        },
                    );
                }
            }
            Ok(())
        },
    )
    .map_err(|error| match error {
        OleanImportError::Bootstrap(source) => {
            ElabError::from(super::ModuleSetupError::LeanWorld {
                world,
                reason: source.to_string(),
            })
        }
        other => fail(other.to_string()),
    })?;
    context.imported_term_syntax = (!handlers.is_empty()).then(|| {
        Arc::new(ImportedTermSyntax {
            source: Arc::from(source),
            handlers,
        })
    });
    runtime.char_program = char_program.and_then(|check| {
        let import = |module_name, is_exported, import_all, is_meta| clean_olean::TypedImport {
            module_name,
            flags: clean_olean::TypedImportFlags::LeanV2 {
                is_exported,
                import_all,
                is_meta,
            },
        };
        let mut imports = Vec::new();
        if !header.is_prelude {
            // Lean.Elab.headerToImports inserts the ordinary and meta imports of Init.
            imports.extend(
                [false, true].map(|meta| import(Name::interned("Init"), true, false, meta)),
            );
        }
        imports.extend(header.imports.iter().map(|i| {
            import(
                i.module.name().clone(),
                i.is_exported,
                i.import_all,
                i.is_meta,
            )
        }));
        check.finish(env, header.is_module, &imports)
    });
    runtime.nat_dictionary = nat_dictionary.and_then(|check| check.finish());
    runtime.stdout_imports = stdout_inputs.and_then(|check| check.finish());
    runtime.io_error_imports = io_error_inputs.and_then(|check| check.finish());
    context.imported_runtime = (!runtime.is_empty()).then(|| Arc::new(runtime));
    context.note_foreign_private_decls(env, true);
    for (module, _) in &roots {
        context.record_compiler_import(module);
    }
    context.refresh_compiler_module(env);
    Ok(prefixes)
}

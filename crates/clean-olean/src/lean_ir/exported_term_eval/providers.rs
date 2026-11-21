// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Resolve compiled calls through the checked imports of an exported elaborator.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use clean_kernel::Environment;

use super::*;
use crate::import::lean_declaration_artifact;
use crate::lean_ir::decode::IrLayout;
use crate::lean_ir::module_ir::{
    check_companion_layout, with_interpreter_part, CapturedIrInput, PartEntries,
};

/// The actual direct, public meta imports of one exported term elaborator's module.
/// Captures share the graph loader's bytes and survive later filesystem changes.
#[derive(Default)]
pub struct ExportedTermProviders {
    modules: HashMap<String, Option<Provider>>,
}

struct Provider {
    module: Name,
    path: PathBuf,
    capture: Arc<CapturedIrInput>,
    digest: OnceLock<[u8; 32]>,
}

impl ExportedTermProviders {
    pub(crate) fn insert(
        &mut self,
        module: Name,
        path: PathBuf,
        capture: Arc<CapturedIrInput>,
        ambiguous: bool,
    ) {
        let label = module.to_string();
        self.modules.insert(
            label,
            (!ambiguous).then_some(Provider {
                module,
                path,
                capture,
                digest: OnceLock::new(),
            }),
        );
    }

    /// Run the handler with calls to declarations owned by its captured public meta imports.
    /// Every call uses the same execution depth and step budget.
    ///
    /// # Errors
    /// Refuses a missing selected body, malformed parts, conflicting ownership, unsupported
    /// host operations, or an invalid elaborator result.
    pub fn evaluate(
        &self,
        env: &Environment,
        bytes: &[u8],
        handler: &Name,
        syntax: ExportedNumeralSyntax<'_>,
    ) -> OleanResult<Expr> {
        evaluate_handler(
            bytes,
            handler,
            syntax,
            Some(&|target| self.lookup(env, target)),
        )
    }

    fn lookup(&self, env: &Environment, target: &Name) -> OleanResult<Option<ProviderDeclaration>> {
        let Some(origin) = lean_declaration_artifact(env, target) else {
            return Ok(None);
        };
        let Some(provider) = self.modules.get(&origin) else {
            return Ok(None);
        };
        let provider = provider.as_ref().ok_or_else(|| {
            refusal(
                target,
                "distinct captured module names have the same artifact ledger label",
            )
        })?;
        let code = selected_code(&provider.module, &provider.path, &provider.capture, target)?;
        if let Some(host) = provider_host::StableHost::for_target(target) {
            let digest = || {
                *provider.digest.get_or_init(|| {
                    let c = &provider.capture;
                    crate::lean_ir::native_owners::selected_module_digest(
                        crate::CapturedModuleBytes {
                            canonical_path: &provider.path,
                            base: &c.base,
                            server: c.server.as_deref(),
                            private: c.private.as_deref(),
                            ir_signature: c.ir_signature.as_deref(),
                            ir: c.ir.as_deref(),
                        },
                    )
                })
            };
            if host.checks(target, &provider.module, &code, digest)
                && host.has_binding(env, target)?
            {
                return Ok(Some(ProviderDeclaration::Host));
            }
        }
        Ok(Some(ProviderDeclaration::Code(code)))
    }
}

fn selected_code(
    module: &Name,
    path: &Path,
    captured: &CapturedIrInput,
    target: &Name,
) -> OleanResult<Rc<Decl>> {
    let header = check_companion_layout(module, path, &captured.base, IrLayout::Lean436)
        .map_err(|e| refusal(target, e))?;
    let base = CompactedRegion::new(&captured.base, header.base_addr);
    let root = base.root_ptr()?;
    let base_part = base.ir_part_entries(root).map_err(|e| refusal(target, e))?;
    // The ledger projects a module name for compatibility. Confirm this exact typed
    // constant in its exported inventory before consulting its code.
    if !crate::lean_ir::native_owners::field_names(&base, root, 1)?.contains(target) {
        return Err(refusal(
            target,
            "declaration absent from the selected provider's exported names",
        ));
    }
    let declaration = |region: &CompactedRegion<'_>, part: &PartEntries| {
        let Some(table) = part.get(DECL_MAP_EXT) else {
            return Ok(None);
        };
        Program::new(region, table, target)?.declaration(target)
    };
    // Lean.IR.findInterpDecl tries getModuleIREntries before getModuleEntries of the
    // selected owner. A captured missing signature means there are no extra IR entries.
    let ir = with_interpreter_part(
        module,
        path,
        Some(captured),
        IrLayout::Lean436,
        base_part.is_module,
        |region, part| Ok(declaration(region, part)),
    )
    .map_err(|e| refusal(target, e))?
    .transpose()?
    .flatten();
    let code = match ir {
        Some(code) => Some(code),
        None => declaration(&base, &base_part)?,
    };
    code.ok_or_else(|| refusal(target, "missing IR declaration in its captured provider"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "requires the original Lean 4.36.0 SDK in CLEAN_LEAN436_LIB"]
    fn direct_sdk_import_keeps_exact_host_rows_and_refuses_shadowed_bindings() {
        use super::super::provider_host::StableHost;
        use crate::lean_ir::types::ExternEntry;

        let lib = PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
        for (owner, names) in [
            (
                "Init.Prelude",
                &[
                    "Lean.Name.mkStr1",
                    "Lean.Name.mkStr2",
                    "Lean.Syntax.isOfKind",
                    "Lean.Syntax.getArg",
                    "Nat.add",
                ][..],
            ),
            ("Init.Meta.Defs", &["Lean.TSyntax.getNat"][..]),
            ("Lean.Expr", &["Lean.mkNatLit"][..]),
        ] {
            let path = lib.join(owner.replace('.', "/")).with_extension("olean");
            let read =
                |ext: &str| Arc::<[u8]>::from(std::fs::read(path.with_extension(ext)).unwrap());
            let capture = CapturedIrInput {
                base: read("olean"),
                private: Some(read("olean.private")),
                server: Some(read("olean.server")),
                ir: Some(read("ir")),
                ir_signature: Some(read("ir.sig")),
            };
            let digest =
                crate::lean_ir::native_owners::selected_module_digest(crate::CapturedModuleBytes {
                    canonical_path: &path,
                    base: &capture.base,
                    server: capture.server.as_deref(),
                    private: capture.private.as_deref(),
                    ir: capture.ir.as_deref(),
                    ir_signature: capture.ir_signature.as_deref(),
                });
            let module = Name::from_string(owner);
            for name in names {
                let target = Name::from_string(name);
                let host = StableHost::for_target(&target).unwrap();
                let code = selected_code(&module, &path, &capture, &target).unwrap();
                assert!(host.checks(&target, &module, &code, || digest), "{name}");
                assert!(!host.checks(&target, &Name::anon().str(owner), &code, || digest));
                assert!(!host.checks(&target, &module, &code, || [0; 32]));
                assert!(StableHost::for_target(&Name::anon().str(*name)).is_none());
                let mut mismatch = code.as_ref().clone();
                let (Decl::Extern { params, .. } | Decl::FDecl { params, .. }) = &mut mismatch;
                params[0].borrow = !params[0].borrow;
                assert!(!host.checks(&target, &module, &mismatch, || digest));
                if *name == "Nat.add" {
                    let mut wrong_symbol = code.as_ref().clone();
                    let Decl::Extern { ext, .. } = &mut wrong_symbol else {
                        panic!("stable Nat.add is an extern")
                    };
                    ext.entries = vec![ExternEntry::Standard {
                        backend: Name::interned("all"),
                        symbol: "different_symbol".to_owned(),
                    }];
                    assert!(!host.checks(&target, &module, &wrong_symbol, || digest));
                }
            }
        }
    }

    #[test]
    fn loaded_provider_ir_precedes_its_exported_stub_and_preserves_typed_ownership() {
        macro_rules! part {
            ($directory:literal, $suffix:literal) => {
                Arc::from(
                    include_bytes!(concat!(
                        env!("CARGO_MANIFEST_DIR"),
                        "/../../tests/fixtures/olean/v4.36.0/",
                        $directory,
                        "/StableFixture/Defs.",
                        $suffix
                    ))
                    .as_slice(),
                )
            };
        }
        let module = Name::from_string("StableFixture.Defs");
        let base = part!("module-ir", "olean");
        let path = Path::new("already-captured/StableFixture/Defs.olean");
        let root = Name::from_string("StableFixture.addOffset");
        let mut capture = CapturedIrInput {
            base,
            private: None,
            server: None,
            ir: None,
            ir_signature: None,
        };
        let stub = selected_code(&module, path, &capture, &root);
        assert!(stub.is_err() || matches!(stub.unwrap().as_ref(), Decl::Extern { .. }));
        for (sig, ir, expected) in [
            (part!("module-ir", "ir.sig"), part!("module-ir", "ir"), 1),
            (
                part!("compiled-nat/replacement", "ir.sig"),
                part!("compiled-nat/replacement", "ir"),
                2,
            ),
        ] {
            capture.ir_signature = Some(sig);
            capture.ir = Some(ir);
            let code = selected_code(&module, path, &capture, &root).unwrap();
            let Decl::FDecl { body, .. } = code.as_ref() else {
                panic!("expected a body");
            };
            let literal = body.instrs.iter().find_map(|i| match i {
                Instr::VDecl {
                    e: IrExpr::Lit(LitVal::Num(n)),
                    ..
                } => Some(n),
                _ => None,
            });
            assert_eq!(literal, Some(&crate::expr::BigNat::from_u64(expected)));
        }
        assert!(selected_code(
            &module,
            path,
            &capture,
            &Name::anon().str("StableFixture.addOffset")
        )
        .is_err());
        let mut foreign = Vec::from(capture.ir.as_deref().unwrap());
        foreign[40] = b'0';
        capture.ir = Some(Arc::from(foreign));
        assert!(selected_code(&module, path, &capture, &root).is_err());
    }
}

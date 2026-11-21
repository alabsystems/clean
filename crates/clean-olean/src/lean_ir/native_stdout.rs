// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source and executable ownership of the stable process stdout externs.

use super::module_ir::{load_module_ir_captured, CapturedIrInput, InterpSource};
use super::native_owners::CapturedPrivateNativeModule;
use super::types::{Decl, ExternEntry, IrType};
use clean_kernel::Name;
use std::sync::Arc;

// Original five-part release inputs, including the source and the native IR.
const MODULES: &[(&str, [u8; 32])] = &[
    (
        "Init.Prelude",
        [
            0x77, 0xa6, 0x27, 0x54, 0xc6, 0xa9, 0xe7, 0x63, 0x7e, 0x0, 0x55, 0x9f, 0xcc, 0x0, 0x5a,
            0xee, 0xc7, 0x12, 0xe6, 0x86, 0xf9, 0xa8, 0xc4, 0x25, 0xbf, 0xa9, 0x48, 0xa1, 0x0,
            0x2c, 0x49, 0xea,
        ],
    ),
    (
        "Init.System.ST",
        [
            0x1a, 0xe4, 0x6, 0xfb, 0xea, 0xac, 0x94, 0x16, 0x3c, 0x34, 0x31, 0xea, 0x13, 0x22,
            0xce, 0xca, 0x84, 0xc9, 0x9b, 0x5a, 0x1e, 0xd, 0x77, 0x1c, 0xfb, 0x17, 0x4, 0xb6, 0xc4,
            0x11, 0xdc, 0x12,
        ],
    ),
    (
        "Init.System.IOError",
        [
            0x9f, 0xd3, 0x82, 0x8b, 0x6b, 0xc7, 0xb9, 0x72, 0x7, 0xe4, 0x59, 0x5c, 0x84, 0x3, 0x62,
            0x56, 0x3f, 0x29, 0x8f, 0xfb, 0x92, 0x80, 0xcc, 0xdd, 0x1b, 0x2e, 0xdf, 0xfd, 0xbb,
            0x59, 0x12, 0x7b,
        ],
    ),
    (
        "Init.System.IO",
        [
            0x30, 0xc8, 0xa, 0xbf, 0x3a, 0x76, 0xb3, 0x27, 0x91, 0x2d, 0xa1, 0xb9, 0xeb, 0x99,
            0x97, 0xbd, 0x72, 0x50, 0xb, 0x3c, 0x3b, 0xfb, 0xd5, 0xf2, 0xda, 0x79, 0xea, 0xf4,
            0x1c, 0xfb, 0xcc, 0x52,
        ],
    ),
];

const EXTERNS: &[(&str, &str)] = &[
    ("IO.getStdout", "lean_get_stdout"),
    ("IO.setStdout", "lean_get_set_stdout"),
    ("IO.FS.Handle.flush", "lean_io_prim_handle_flush"),
    ("IO.FS.Handle.read", "lean_io_prim_handle_read"),
    ("IO.FS.Handle.write", "lean_io_prim_handle_write"),
    ("IO.FS.Handle.getLine", "lean_io_prim_handle_get_line"),
    ("IO.FS.Handle.putStr", "lean_io_prim_handle_put_str"),
    ("IO.FS.Handle.isTty", "lean_io_prim_handle_is_tty"),
];

/// Captures the original source and backend records before module registration.
#[derive(Default)]
pub struct StableStdoutImportCheck {
    modules: [bool; 4],
    refused: bool,
}

impl StableStdoutImportCheck {
    /// Inspect the source and native IR chosen by the ordinary file importer.
    pub fn observe(&mut self, capture: &CapturedPrivateNativeModule<'_, '_>) {
        if self.refused {
            return;
        }
        if let Some(i) = MODULES
            .iter()
            .position(|(n, _)| *capture.name == Name::interned(n))
        {
            self.refused = self.modules[i] || capture.digest() != MODULES[i].1;
            self.modules[i] = true;
            if !self.refused && *capture.name == Name::interned("Init.System.IO") {
                self.refused = !original_stdout_ir(capture);
            }
        } else {
            let shadows = |names: &[Name]| {
                names.iter().any(|name| {
                    EXTERNS.iter().any(|(n, _)| *name == Name::interned(n))
                        || *name == Name::interned("IO.FS.Stream.ofHandle")
                })
            };
            self.refused = capture.owners().is_none_or(shadows)
                || capture
                    .public_owners()
                    .map_or(true, |names| shadows(&names));
        }
    }

    /// A missing part, changed record or second owner cannot select this runtime.
    pub fn finish(self) -> Option<StableStdoutImports> {
        (!self.refused && self.modules.iter().all(|seen| *seen)).then_some(StableStdoutImports(()))
    }
}

/// The checked original environment provided this particular system stream.
pub struct StableStdoutImports(());

impl StableStdoutImports {
    /// Recheck the registered implementation of every method on the default stream.
    pub fn check_externs(&self, env: &clean_kernel::Environment) -> bool {
        use clean_kernel::env::{CompilerExternArity, CompilerExternEntry, CompilerExternMetadata};
        EXTERNS.iter().all(|(n,symbol)| {
            let name=Name::interned(n);
            crate::import::lean_declaration_artifact(env,&name).as_deref()==Some("Init.System.IO")
                && !env.is_unsafe(&name) && !env.is_partial(&name)
                && !env.is_noncomputable(&name) && !env.has_implemented_by(&name)
                && matches!(env.extern_metadata(&name), Ok(Some(CompilerExternMetadata::Complete(ref d)))
                    if d.arity==CompilerExternArity::Unspecified && matches!(d.entries.as_slice(),
                      [CompilerExternEntry::Standard { backend, symbol: target }]
                      if *backend==Name::interned("all") && target==symbol))
        })
    }
}

fn original_stdout_ir(capture: &CapturedPrivateNativeModule<'_, '_>) -> bool {
    use IrType::{Object as O, TObject as T, UInt8, USize, Void};
    let p = capture.parts;
    let parts = CapturedIrInput {
        base: Arc::from(p.base),
        server: p.server.map(Arc::from),
        private: p.private.map(Arc::from),
        ir: p.ir.map(Arc::from),
        ir_signature: p.ir_signature.map(Arc::from),
    };
    let Ok(module) = load_module_ir_captured(capture.name, p.canonical_path, &parts) else {
        return false;
    };
    if module.interp_source != InterpSource::IrFile {
        return false;
    }
    let shapes: &[(&[(IrType, bool)], IrType)] = &[
        (&[(Void, false)], O),
        (&[(O, false), (Void, false)], O),
        (&[(T, true), (Void, false)], O),
        (&[(T, true), (USize, false), (Void, false)], O),
        (&[(T, true), (O, true), (Void, false)], O),
        (&[(T, true), (Void, false)], O),
        (&[(T, true), (O, true), (Void, false)], O),
        (&[(T, true), (Void, false)], UInt8),
    ];
    EXTERNS
        .iter()
        .zip(shapes)
        .all(|((n, symbol), (args, result))| {
            let name = Name::interned(n);
            let mut records = module.ir_decls().iter().filter(|r| *r.name() == name);
            let Some(Decl::Extern {
                params, ty, ext, ..
            }) = records.next()
            else {
                return false;
            };
            records.next().is_none()
                && ty == result
                && params.len() == args.len()
                && params
                    .iter()
                    .zip(*args)
                    .all(|(param, (t, b))| param.ty == *t && param.borrow == *b)
                && matches!(ext.entries.as_slice(),[ExternEntry::Standard {backend,symbol:target}]
                if *backend==Name::interned("all") && target==symbol)
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, LeanWorld};

    #[test]
    #[ignore = "requires the genuine Lean 4.36.0 SDK in CLEAN_LEAN436_LIB"]
    fn original_stdout_requires_the_actual_source_ir_and_unique_runtime_owners() {
        let root = std::path::PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
        let mut env = Environment::new();
        crate::declare_environment_world(&mut env, LeanWorld::Lean436.tag()).unwrap();
        let mut original = StableStdoutImportCheck::default();
        let mut absent = StableStdoutImportCheck::default();
        let mut changed = StableStdoutImportCheck::default();
        let mut repeated = StableStdoutImportCheck::default();
        let mut other = StableStdoutImportCheck::default();
        crate::load_modules_with_deps_checked(
            &mut env,
            &["Init.System.IO".to_string()],
            &[root],
            &mut |_, _, _| Ok(()),
            &mut |module, _, parts| {
                let input = CapturedPrivateNativeModule::new(module, parts);
                original.observe(&input);
                repeated.observe(&input);
                other.observe(&input);
                if *module == Name::interned("Init.System.IO") {
                    repeated.observe(&input);
                    let mut bytes = parts.ir.unwrap().to_vec();
                    let end = bytes.len() - 1;
                    bytes[end] ^= 1;
                    changed.observe(&CapturedPrivateNativeModule::new(
                        module,
                        crate::CapturedModuleBytes {
                            ir: Some(&bytes),
                            ..parts
                        },
                    ));
                    other.observe(&CapturedPrivateNativeModule::new(
                        &Name::interned("Other"),
                        parts,
                    ));
                } else {
                    absent.observe(&input);
                    changed.observe(&input);
                }
                Ok(())
            },
        )
        .unwrap();
        let original = original.finish().expect("original SDK stdout");
        assert!(original.check_externs(&env));
        for invalid in [absent, changed, repeated, other] {
            assert!(invalid.finish().is_none());
        }
        env.register_extern(Name::interned("IO.getStdout"), "wrong_stdout".to_owned());
        assert!(!original.check_externs(&env));
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The original stable Char.ofNat program, its compiler-generated zero and its externs.
use super::module_ir::{load_module_ir_captured, CapturedIrInput, InterpSource};
use super::native_owners::{
    CapturedPrivateNativeModule, NativeImportHeaders, STABLE_PRELUDE_DIGEST as ORIGINAL,
};
mod phases;
use crate::TypedImport;
use clean_kernel::{ConstantInfo, Environment, LeanWorld, Name};
use std::collections::HashMap;
use std::sync::Arc;

const PRELUDE: &str = "Init.Prelude";
const ROWS: [&str; 5] = [
    "Char.ofNat",
    "Char.ofNat._closed_0",
    "Nat.decLt",
    "Char.ofNatAux",
    "UInt32.ofBitVec",
];

/// Accumulates the original records and positive import paths for this source header.
#[derive(Default)]
pub struct StableCharProgramCheck {
    seen: bool,
    refused: bool,
    imports: HashMap<Name, NativeImportHeaders>,
}
impl StableCharProgramCheck {
    /// Observe every checked module, including those that can shadow a generated IR name.
    pub fn observe(&mut self, m: &CapturedPrivateNativeModule<'_, '_>) {
        if self.refused {
            return;
        }
        let Some(imports) = m.phase_imports() else {
            self.refused = true;
            return;
        };
        if self
            .imports
            .insert(m.name.clone(), imports.clone())
            .is_some()
        {
            self.refused = true;
            return;
        }
        if *m.name == Name::interned(PRELUDE) {
            self.seen = m.digest() == ORIGINAL && original_rows(m);
            self.refused = !self.seen;
        } else {
            let shadows = |ns: &[Name]| ROWS.iter().any(|n| ns.contains(&Name::interned(n)));
            self.refused =
                m.owners().is_none_or(shadows) || m.public_owners().map_or(true, |n| shadows(&n));
        }
    }

    /// Require both IR phases for the original Prelude, or the private import mode
    /// that selects all phases. Roots retain the order and flags of the source header.
    pub fn finish(
        self,
        env: &Environment,
        inside_module: bool,
        roots: &[TypedImport],
    ) -> Option<StableCharProgram> {
        if self.refused
            || !self.seen
            || roots
                .iter()
                .any(|i| !self.imports.contains_key(&i.module_name))
            || !self.all_phases(inside_module, roots)
        {
            return None;
        }
        let infos = ROWS
            .iter()
            .filter(|s| **s != ROWS[1])
            .map(|n| env.get_const(&Name::interned(n)).cloned())
            .collect::<Option<Vec<_>>>()?;
        let result = StableCharProgram(infos.into());
        result.matches_environment(env).then_some(result)
    }
}

/// The immutable selected executable and its registered source declarations.
pub struct StableCharProgram(Arc<[ConstantInfo]>);
impl StableCharProgram {
    /// Check that the source records which authorized the native dependency still agree.
    pub fn matches_environment(&self, env: &Environment) -> bool {
        crate::environment_world(env) == Some(LeanWorld::Lean436.tag())
            && self.0.iter().all(|i| {
                env.get_const(&i.name) == Some(i)
                    && crate::import::lean_declaration_artifact(env, &i.name).as_deref()
                        == Some(PRELUDE)
            })
            && ROWS.iter().all(|n| {
                let name = Name::interned(n);
                !env.has_implemented_by(&name)
                    && !env.is_unsafe(&name)
                    && !env.is_partial(&name)
                    && !env.is_noncomputable(&name)
                    && !clean_kernel::env::csimp::has_replacement(env, &name)
            })
            && env.get_const(&Name::interned(ROWS[1])).is_none()
    }
}

fn original_rows(m: &CapturedPrivateNativeModule<'_, '_>) -> bool {
    let p = m.parts;
    let parts = CapturedIrInput {
        base: Arc::from(p.base),
        server: p.server.map(Arc::from),
        private: p.private.map(Arc::from),
        ir_signature: p.ir_signature.map(Arc::from),
        ir: p.ir.map(Arc::from),
    };
    let Ok(program) = load_module_ir_captured(m.name, p.canonical_path, &parts) else {
        return false;
    };
    program.interp_source == InterpSource::IrFile
        && ROWS.iter().all(|n| {
            let name = Name::interned(n);
            program
                .ir_decls()
                .iter()
                .filter(|r| r.name() == &name)
                .count()
                == 1
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TypedImportFlags;
    use std::path::PathBuf;

    fn import(name: &str, all: bool, meta: bool) -> TypedImport {
        TypedImport {
            module_name: Name::interned(name),
            flags: TypedImportFlags::LeanV2 {
                is_exported: true,
                import_all: all,
                is_meta: meta,
            },
        }
    }

    fn headers(edges: Vec<TypedImport>) -> NativeImportHeaders {
        let shared: Arc<[TypedImport]> = edges.into();
        NativeImportHeaders {
            is_module: true,
            public: shared.clone(),
            private: shared.clone(),
            ir: Some(shared),
        }
    }

    #[test]
    fn private_and_meta_edges_only_contribute_their_selected_phases() {
        let root = |all, meta| import("Intermediate", all, meta);
        let check = |is_exported, import_all, is_meta| {
            let edge = TypedImport {
                module_name: Name::interned(PRELUDE),
                flags: TypedImportFlags::LeanV2 {
                    is_exported,
                    import_all,
                    is_meta,
                },
            };
            StableCharProgramCheck {
                imports: HashMap::from([
                    (Name::interned("Intermediate"), headers(vec![edge])),
                    (Name::interned(PRELUDE), headers(vec![])),
                ]),
                ..Default::default()
            }
        };
        let both = [root(false, false), root(false, true)];
        assert!(check(true, false, false).all_phases(true, &both));
        assert!(!check(false, false, false).all_phases(true, &both));
        assert!(!check(true, false, true).all_phases(true, &both));
        assert!(check(false, true, false).all_phases(true, &[root(true, false)]));
        assert!(!check(false, false, false).all_phases(true, &[root(true, false)]));
        assert!(check(false, false, false).all_phases(false, &[root(false, false)]));
    }

    #[test]
    fn revisiting_an_import_uses_its_prior_main_module_and_incoming_flags() {
        let private_b = TypedImport {
            module_name: Name::interned("B"),
            flags: TypedImportFlags::LeanV2 {
                is_exported: false,
                import_all: false,
                is_meta: false,
            },
        };
        let mut b = headers(vec![import(PRELUDE, false, false)]);
        b.ir = None;
        let check = StableCharProgramCheck {
            imports: HashMap::from([
                (Name::interned("M"), headers(vec![private_b])),
                (Name::interned("B"), b),
                (Name::interned(PRELUDE), headers(vec![])),
            ]),
            ..Default::default()
        };
        let m = import("M", false, true);
        let b = import("B", false, false);
        let prelude = import(PRELUDE, false, false);
        // B first has data. The later IR-only visit propagates comptime through
        // the prior data header, using the incoming visit's flags.
        assert!(check.all_phases(true, &[prelude.clone(), b.clone(), m.clone()]));
        // B first has only its empty IR header. The data upgrade revisits that
        // prior header; the direct Prelude import contributes runtime alone.
        assert!(!check.all_phases(true, &[prelude, m, b]));
    }

    #[test]
    #[ignore = "requires the original CLEAN_LEAN436_LIB"]
    fn ir_only_imports_follow_the_original_ir_header_and_stop_without_it() {
        let sdk = PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
        let mut env = Environment::for_lean_replay();
        crate::declare_environment_world(&mut env, LeanWorld::Lean436.tag()).unwrap();
        let mut original = StableCharProgramCheck::default();
        let mut missing = StableCharProgramCheck::default();
        let mut saw_notation = false;
        crate::load_modules_with_deps_checked(
            &mut env,
            &["Init.LetFun".into()],
            &[sdk],
            &mut |_, _, _| Ok(()),
            &mut |name, _, parts| {
                let module = CapturedPrivateNativeModule::new(name, parts);
                original.observe(&module);
                if *name == Name::interned("Init.Notation") {
                    let headers = module.phase_imports().unwrap();
                    assert!(headers
                        .ir
                        .as_deref()
                        .unwrap()
                        .iter()
                        .any(|i| i.module_name == Name::interned("Init.Coe")));
                    saw_notation = true;
                    missing.observe(&CapturedPrivateNativeModule::new(
                        name,
                        crate::CapturedModuleBytes {
                            ir_signature: None,
                            ir: None,
                            ..parts
                        },
                    ));
                } else {
                    missing.observe(&module);
                }
                Ok(())
            },
        )
        .unwrap();
        assert!(saw_notation);
        // Init.LetFun privately imports Init.Notation. A meta import of the former
        // reaches the latter in IR-only mode; its IR reaches Init.Prelude via Init.Coe.
        let roots = [
            import(PRELUDE, false, false),
            import("Init.LetFun", false, true),
        ];
        let notation = import("Init.Notation", false, false);
        let [ref p, ref m] = roots;
        // Official importModules on the missing-IR graph reports .all for
        // dataThenMeta and .runtime for metaThenData.
        assert!(missing.all_phases(true, &[p.clone(), notation.clone(), m.clone()]));
        assert!(!missing.all_phases(true, &[p.clone(), m.clone(), notation]));
        // Two independent Prelude phases do not repair missing data for another module.
        assert!(!missing.all_phases(true, &[p.clone(), import(PRELUDE, false, true), m.clone()]));
        assert!(original.finish(&env, true, &roots).is_some());
        assert!(missing.finish(&env, true, &roots).is_none());
    }

    #[test]
    #[ignore = "requires the original CLEAN_LEAN436_LIB"]
    fn original_char_ir_matches_the_official_private_init_program() {
        use crate::lean_ir::format_decl::format_decl;
        use crate::lean_ir::module_ir::{load_module_ir_at, InterpSource};
        use crate::lean_ir::types::{Decl, ExternEntry};
        use std::fmt::Write;

        let root = PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
        let module = load_module_ir_at(
            &Name::interned("Init.Prelude"),
            &root.join("Init/Prelude.olean"),
        )
        .unwrap();
        assert_eq!(module.interp_source, InterpSource::IrFile);
        let mut result = String::new();
        for text in ROWS {
            let name = Name::interned(text);
            let mut found = module.ir_decls().iter().filter(|decl| decl.name() == &name);
            let row = found.next().expect("original selected row");
            assert!(found.next().is_none());
            writeln!(result, "{}", format_decl(row)).unwrap();
            match row {
                Decl::FDecl { info, .. } => assert!(info.sorry_dep.is_none()),
                Decl::Extern { ext, .. } => {
                    let [ExternEntry::Standard { backend, symbol }] = ext.entries.as_slice() else {
                        panic!("unexpected extern alternatives for {text}");
                    };
                    writeln!(result, "{backend} {symbol}").unwrap();
                }
            }
        }
        assert_eq!(
            result,
            include_str!("../../tests/fixtures/lean/StablePrivateChar436.stdout")
        );
    }

    #[test]
    #[ignore = "requires the original CLEAN_LEAN436_LIB"]
    fn selected_original_code_requires_all_phases_and_original_bytes() {
        let sdk = PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
        let mut env = Environment::for_lean_replay();
        crate::declare_environment_world(&mut env, LeanWorld::Lean436.tag()).unwrap();
        let mut checks: [_; 7] = std::array::from_fn(|_| StableCharProgramCheck::default());
        let prelude = Name::interned(PRELUDE);
        crate::load_modules_with_deps_checked(
            &mut env,
            &[PRELUDE.into()],
            &[sdk],
            &mut |_, _, _| Ok(()),
            &mut |name, _, parts| {
                let module = CapturedPrivateNativeModule::new(name, parts);
                for (i, c) in checks.iter_mut().enumerate() {
                    if name == &prelude && i == 4 {
                        let mut ir = parts.ir.unwrap().to_vec();
                        *ir.last_mut().unwrap() ^= 1;
                        c.observe(&CapturedPrivateNativeModule::new(
                            name,
                            crate::CapturedModuleBytes {
                                ir: Some(&ir),
                                ..parts
                            },
                        ));
                    } else if name == &prelude && i == 5 {
                        c.observe(&CapturedPrivateNativeModule::new(
                            name,
                            crate::CapturedModuleBytes {
                                ir_signature: None,
                                ..parts
                            },
                        ));
                    } else {
                        c.observe(&module);
                        if name == &prelude && i == 6 {
                            c.observe(&CapturedPrivateNativeModule::new(
                                &Name::anon().str("Init.Prelude"),
                                parts,
                            ));
                        }
                    }
                }
                Ok(())
            },
        )
        .unwrap();
        let [all, both, meta, runtime, changed, missing, shadow] = checks;
        let all_root = [import(PRELUDE, true, false)];
        let witness = all.finish(&env, true, &all_root).unwrap();
        assert!(both
            .finish(
                &env,
                true,
                &[import(PRELUDE, false, false), import(PRELUDE, false, true)]
            )
            .is_some());
        assert!(meta
            .finish(&env, true, &[import(PRELUDE, false, true)])
            .is_none());
        assert!(runtime
            .finish(&env, true, &[import(PRELUDE, false, false)])
            .is_none());
        for c in [changed, missing, shadow] {
            assert!(c.finish(&env, true, &all_root).is_none());
        }
        env.register_implemented_by(Name::interned("Char.ofNat"), Name::interned("alternative"));
        assert!(!witness.matches_environment(&env));
    }
}

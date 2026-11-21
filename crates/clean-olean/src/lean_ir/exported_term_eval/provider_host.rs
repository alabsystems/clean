// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Host representations of the seven bounded operations in Lean 4.36.0.
//! A direct provider can use a host operation only when its selected owner,
//! five-part release digest, typed declaration and binding agree.

use clean_kernel::env::{CompilerExternArity, CompilerExternEntry, CompilerExternMetadata};
use clean_kernel::Environment;

use super::{host_operation, refusal, Decl, IrType, Name, OleanResult};
use crate::lean_ir::native_owners::STABLE_PRELUDE_DIGEST;
use crate::lean_ir::types::ExternEntry;

const META_DEFS: [u8; 32] = [
    0x9c, 0x2b, 0x9c, 0xe9, 0xd5, 0x34, 0x1a, 0xe4, 0x08, 0xfc, 0x52, 0xbc, 0x50, 0xab, 0x5b, 0x36,
    0x9d, 0xef, 0xba, 0xfd, 0x63, 0x63, 0xf7, 0x3d, 0x7d, 0x5a, 0xd7, 0x7d, 0x11, 0x68, 0x2a, 0x28,
];
const LEAN_EXPR: [u8; 32] = [
    0x78, 0x7a, 0x1d, 0xac, 0x15, 0x97, 0x6e, 0xe6, 0x9e, 0xdd, 0x71, 0x4a, 0xd8, 0xfa, 0xc6, 0x49,
    0x90, 0x99, 0x42, 0xbd, 0x13, 0x43, 0x07, 0xbe, 0x75, 0x47, 0x35, 0xe6, 0x92, 0xa3, 0xbc, 0x6d,
];

pub(super) struct StableHost {
    owner: &'static str,
    digest: [u8; 32],
    params: &'static [(IrType, bool)],
    result: IrType,
    symbol: Option<&'static str>,
}

impl StableHost {
    pub(super) fn for_target(name: &Name) -> Option<Self> {
        use IrType::{Object, TObject, UInt8};
        let mut host = Self {
            owner: "Init.Prelude",
            digest: STABLE_PRELUDE_DIGEST,
            params: &[],
            result: TObject,
            symbol: None,
        };
        host.params = match host_operation(name)? {
            "Lean.Name.mkStr1" => &[(Object, false)],
            "Lean.Name.mkStr2" => &[(Object, false), (Object, false)],
            "Lean.Syntax.isOfKind" => {
                host.result = UInt8;
                &[(TObject, false), (TObject, true)]
            }
            "Lean.Syntax.getArg" => &[(TObject, true), (TObject, true)],
            "Lean.TSyntax.getNat" => {
                host.owner = "Init.Meta.Defs";
                host.digest = META_DEFS;
                &[(TObject, true)]
            }
            "Nat.add" => {
                host.symbol = Some("lean_nat_add");
                &[(TObject, true), (TObject, true)]
            }
            "Lean.mkNatLit" => {
                host.owner = "Lean.Expr";
                host.digest = LEAN_EXPR;
                host.result = Object;
                &[(TObject, false)]
            }
            _ => return None,
        };
        Some(host)
    }

    pub(super) fn checks(
        &self,
        target: &Name,
        owner: &Name,
        decl: &Decl,
        digest: impl FnOnce() -> [u8; 32],
    ) -> bool {
        if *owner != Name::interned(self.owner) || decl.name() != target {
            return false;
        }
        let (params, ty) = match (self.symbol, decl) {
            (
                None,
                Decl::FDecl {
                    params, ty, info, ..
                },
            ) if info.sorry_dep.is_none() => (params, ty),
            (
                Some(symbol),
                Decl::Extern {
                    params, ty, ext, ..
                },
            ) if matches!(ext.entries.as_slice(),
                [ExternEntry::Standard {backend,symbol:found}] if *backend == Name::interned("all") && found == symbol
            ) =>
            {
                (params, ty)
            }
            _ => return false,
        };
        *ty == self.result
            && params
                .iter()
                .map(|p| (&p.ty, p.borrow))
                .eq(self.params.iter().map(|(ty, b)| (ty, *b)))
            && digest() == self.digest
    }

    pub(super) fn has_binding(&self, env: &Environment, target: &Name) -> OleanResult<bool> {
        if env.has_implemented_by(target) {
            return Ok(false);
        }
        let Some(symbol) = self.symbol else {
            return Ok(true);
        };
        let binding = env
            .extern_metadata(target)
            .map_err(|e| refusal(target, e))?;
        Ok(
            matches!(binding, Some(CompilerExternMetadata::Complete(descriptor))
            if descriptor.arity == CompilerExternArity::Unspecified
                && matches!(descriptor.entries.as_slice(),
                    [CompilerExternEntry::Standard { backend, symbol: actual }]
                    if *backend == Name::interned("all") && actual == symbol)),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::CompilerExternDescriptor;

    #[test]
    fn selected_nat_add_extern_must_still_be_the_registered_binding() {
        let target = Name::interned("Nat.add");
        let host = StableHost::for_target(&target).unwrap();
        let mut env = Environment::default();
        assert!(!host.has_binding(&env, &target).unwrap());
        env.register_extern_metadata(
            target.clone(),
            CompilerExternMetadata::Complete(CompilerExternDescriptor {
                arity: CompilerExternArity::Unspecified,
                entries: vec![CompilerExternEntry::Standard {
                    backend: Name::interned("all"),
                    symbol: "lean_nat_add".into(),
                }],
            }),
        )
        .unwrap();
        assert!(host.has_binding(&env, &target).unwrap());
        let mut replaced = env.clone();
        replaced.register_implemented_by(target.clone(), Name::interned("other"));
        assert!(!host.has_binding(&replaced, &target).unwrap());
        env.register_extern(target.clone(), "lean_nat_add".into());
        assert!(!host.has_binding(&env, &target).unwrap());
    }
}

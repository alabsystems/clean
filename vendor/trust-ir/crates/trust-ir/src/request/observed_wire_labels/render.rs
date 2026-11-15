// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[derive(Clone, Copy)]
enum Location {
    Module,
    Node(WireNodeSite),
    Scope { function: u32, scope: u32 },
    Signature(usize),
    Count { what: &'static str, count: u64 },
}
impl Render {
    pub(super) fn map<O: ExecutionObserver>(
        &mut self,
        m: &Module,
        row: &BinaryProjectionError,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(7, size_of::<Location>() + size_of::<&'static str>())?;
        let (kind, construct) = match row {
            BinaryProjectionError::ConstructAheadOfWireTag {
                construct,
                site: Some(site),
            } => (Location::Node(*site), *construct),
            BinaryProjectionError::ConstructAheadOfWireTag {
                construct,
                site: None,
            } => (Location::Module, *construct),
            BinaryProjectionError::InlinedScopeChainUnencodable { function, scope } => (
                Location::Scope {
                    function: *function,
                    scope: *scope,
                },
                "ScopeData.inlined_at",
            ),
            BinaryProjectionError::CompletenessClaimUnencodable => {
                (Location::Module, "Module.completeness")
            }
            BinaryProjectionError::SignatureAbiUnencodable { signature, .. } => (
                Location::Signature(*signature),
                "FuncTy.abi (a typed signature ABI past its encoding limits)",
            ),
            BinaryProjectionError::ProducerInternalType => {
                (Location::Module, "Ty::Error (producer-internal)")
            }
            BinaryProjectionError::CountExceedsFormat { what, count } => (
                Location::Count {
                    what,
                    count: *count,
                },
                "a count past the binary format's u32 limit",
            ),
            _ => (Location::Module, "a construct the binary writer refuses"),
        };
        match kind {
            Location::Module => w.text("module", &mut self.text)?,
            Location::Node(site) => {
                self.function(m, site.function, w)?;
                w.text("' bb", &mut self.text)?;
                w.decimal(u128::from(site.block), &mut self.text)?;
                w.text(" #", &mut self.text)?;
                w.decimal(site.index as u128, &mut self.text)?;
            }
            Location::Scope { function, scope } => {
                self.function(m, function, w)?;
                w.text("' lexical scope #", &mut self.text)?;
                w.decimal(u128::from(scope), &mut self.text)?;
            }
            Location::Signature(index) => {
                w.text("signature #", &mut self.text)?;
                w.decimal(index as u128, &mut self.text)?;
            }
            Location::Count { what, count } => {
                w.text(what, &mut self.text)?;
                w.text(" (", &mut self.text)?;
                w.decimal(u128::from(count), &mut self.text)?;
                w.text(" entries)", &mut self.text)?;
            }
        }
        self.emit(construct, w)
    }
    fn function<O: ExecutionObserver>(
        &mut self,
        m: &Module,
        id: u32,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.text("function '", &mut self.text)?;
        let name = Self::lookup(m, FuncId::new(id), w)?.map_or("?", |f| f.name.as_str());
        w.text(name, &mut self.text)
    }
}

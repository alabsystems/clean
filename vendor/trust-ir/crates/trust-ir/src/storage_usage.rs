//! One policy for addressable storage geometry versus typed value traffic.
//!
//! This scan is ordinary module validation, not a bounded/certifying observer.
//! It names no active field and grants no initialized value or pointer permission.
use crate::{Inst, LayoutTable, Module, StorageLayout};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StorageSite {
    TypeOccurrence(usize),
    Signature {
        signature: usize,
        result: bool,
        slot: usize,
    },
    Global(usize),
    DropGlue(usize),
    BlockParameter {
        function: usize,
        block: usize,
        parameter: usize,
    },
    Instruction {
        function: usize,
        block: usize,
        instruction: usize,
    },
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StorageViolationKind {
    InvalidGeometry(StorageLayout),
    ValueTraffic,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StorageViolation {
    pub site: StorageSite,
    pub kind: StorageViolationKind,
}

impl Module {
    /// A complete scan; `Alloca` and `GEP` may spell storage geometry, while
    /// every other typed instruction and every SSA/ABI slot must be value-capable.
    /// Aggregate declarations themselves describe addressable geometry and are
    /// allowed. Pointer/ref pointees do not become values of their referent type.
    pub fn visit_storage_violations(
        &self,
        layouts: &LayoutTable<'_>,
        mut emit: impl FnMut(StorageViolation),
    ) {
        let mut occurrence = 0usize;
        let mut has_storage = false;
        self.visit_types(|ty| {
            if let crate::Ty::Storage(layout) = ty {
                has_storage = true;
                if !layout.is_well_formed(self.pointer_bits()) {
                    emit(StorageViolation {
                        site: StorageSite::TypeOccurrence(occurrence),
                        kind: StorageViolationKind::InvalidGeometry(*layout),
                    });
                }
            }
            occurrence = occurrence.saturating_add(1);
        });
        // The inventory above includes unused declarations, every table member,
        // and all instruction roots. StorageValue reachability has Storage as
        // its only seed (unlike the separate strict StorageClosed predicate).
        // With no seed anywhere, every subsequent by-value query is false.
        // A caller may supply a different module's layout table: its named
        // references can reach seeds absent here, so preserve that full scan.
        // Keep the full path unchanged as soon as any Storage occurs.
        if !has_storage && core::ptr::eq(self, layouts.module()) {
            return;
        }
        let mut value = |ty: &crate::Ty, site| {
            if layouts.type_contains_storage_by_value(ty) {
                emit(StorageViolation {
                    site,
                    kind: StorageViolationKind::ValueTraffic,
                });
            }
        };
        for (signature, sig) in self.func_types.iter().enumerate() {
            for (result, types) in [(false, &sig.params), (true, &sig.returns)] {
                for (slot, ty) in types.iter().enumerate() {
                    value(
                        ty,
                        StorageSite::Signature {
                            signature,
                            result,
                            slot,
                        },
                    );
                }
            }
        }
        for (index, global) in self.globals.iter().enumerate() {
            value(&global.ty, StorageSite::Global(index));
        }
        for (index, row) in self.drop_glue.iter().enumerate() {
            value(&row.ty, StorageSite::DropGlue(index));
        }
        for (index, function) in self.functions.iter().enumerate() {
            self.visit_function_storage_violations(function, index, layouts, &mut emit);
        }
    }

    pub fn visit_function_storage_violations(
        &self,
        source: &crate::Function,
        function: usize,
        layouts: &LayoutTable<'_>,
        mut emit: impl FnMut(StorageViolation),
    ) {
        let mut check = |ty: &crate::Ty, site, value| {
            ty.visit_types(|child| {
                if let crate::Ty::Storage(layout) = child
                    && !layout.is_well_formed(self.pointer_bits())
                {
                    emit(StorageViolation {
                        site,
                        kind: StorageViolationKind::InvalidGeometry(*layout),
                    });
                }
            });
            if value && layouts.type_contains_storage_by_value(ty) {
                emit(StorageViolation {
                    site,
                    kind: StorageViolationKind::ValueTraffic,
                });
            }
        };
        for (block, body) in source.blocks.iter().enumerate() {
            for (parameter, (_, ty)) in body.params.iter().enumerate() {
                check(
                    ty,
                    StorageSite::BlockParameter {
                        function,
                        block,
                        parameter,
                    },
                    true,
                );
            }
            for (instruction, node) in body.body.iter().enumerate() {
                let value = !matches!(node.inst, Inst::Alloca { .. } | Inst::GEP { .. });
                node.inst.visit_type_roots(|ty| {
                    check(
                        ty,
                        StorageSite::Instruction {
                            function,
                            block,
                            instruction,
                        },
                        value,
                    )
                });
            }
        }
    }

    /// First refusing witness. No authority or value is produced by this query.
    pub fn first_storage_violation(&self) -> Option<StorageViolation> {
        let layouts = self.layout_table();
        let mut first = None;
        self.visit_storage_violations(&layouts, |error| {
            if first.is_none() {
                first = Some(error);
            }
        });
        first
    }
}

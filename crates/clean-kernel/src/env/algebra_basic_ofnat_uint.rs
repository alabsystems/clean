// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OfNat instances for UInt types (UInt8, UInt16, UInt32, UInt64, USize)
//!
//! Split from algebra_basic.rs for #307.
//! OfNat typeclass definition is in algebra_basic_ofnat.rs.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment, KernelInstanceInfo};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    // ========================================================================
    // OfNat instances for UInt types
    // ========================================================================

    /// Initialize OfNat instance for UInt8
    ///
    /// ```text
    /// instance (n : Nat) : OfNat UInt8 n where
    ///   ofNat := UInt8.mk n
    /// ```
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ofnat_uint8_inst_init == true`
    /// ENSURES: On success, required dependencies (`ofnat`, `uint8`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_ofnat_uint8(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Fin-carrier / v4.8-shape carrier cluster (see init_uint8..64) —
        // suppressed in import mode so the genuine v4.31 declarations import.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.ofnat_uint8_inst_init {
            return Ok(());
        }

        self.init_ofnat()?;
        self.init_uint8()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let uint8_const = Expr::const_(Name::from_string("UInt8"), vec![]);
        let ofnat_const = Expr::const_(Name::from_string("OfNat"), vec![Level::zero()]);
        let ofnat_mk = Expr::const_(Name::from_string("OfNat.mk"), vec![Level::zero()]);
        let uint8_ofnat = Expr::const_(Name::from_string("UInt8.ofNat"), vec![]);

        // instOfNatUInt8 : (n : Nat) → OfNat UInt8 n
        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let e = Expr::app(
                Expr::app(ofnat_const.clone(), uint8_const.clone()),
                n.clone(),
            );
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // value: λ n : Nat => OfNat.mk UInt8 n (UInt8.mk n)
        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(Expr::app(ofnat_mk.clone(), uint8_const.clone()), n.clone()),
                Expr::app(uint8_ofnat.clone(), n.clone()),
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        self.ensure_exact_checked_decl(Declaration::Definition {
            name: Name::from_string("instOfNatUInt8"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.ensure_exact_instance(KernelInstanceInfo {
            name: Name::from_string("instOfNatUInt8"),
            class_name: Name::from_string("OfNat"),
            priority: 100,
            type_: None,
            value: None,
        })?;

        self.ofnat_uint8_inst_init = true;
        Ok(())
    }

    /// Check if OfNat UInt8 instance has been initialized
    pub(crate) fn has_ofnat_uint8(&self) -> bool {
        self.ofnat_uint8_inst_init
    }

    /// Initialize OfNat instance for UInt16
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ofnat_uint16_inst_init == true`
    /// ENSURES: On success, required dependencies (`ofnat`, `uint16`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_ofnat_uint16(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Fin-carrier / v4.8-shape carrier cluster (see init_uint8..64) —
        // suppressed in import mode so the genuine v4.31 declarations import.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.ofnat_uint16_inst_init {
            return Ok(());
        }

        self.init_ofnat()?;
        self.init_uint16()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let uint16_const = Expr::const_(Name::from_string("UInt16"), vec![]);
        let ofnat_const = Expr::const_(Name::from_string("OfNat"), vec![Level::zero()]);
        let ofnat_mk = Expr::const_(Name::from_string("OfNat.mk"), vec![Level::zero()]);
        let uint16_ofnat = Expr::const_(Name::from_string("UInt16.ofNat"), vec![]);

        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let e = Expr::app(
                Expr::app(ofnat_const.clone(), uint16_const.clone()),
                n.clone(),
            );
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(Expr::app(ofnat_mk.clone(), uint16_const.clone()), n.clone()),
                Expr::app(uint16_ofnat.clone(), n.clone()),
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        self.ensure_exact_checked_decl(Declaration::Definition {
            name: Name::from_string("instOfNatUInt16"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.ensure_exact_instance(KernelInstanceInfo {
            name: Name::from_string("instOfNatUInt16"),
            class_name: Name::from_string("OfNat"),
            priority: 100,
            type_: None,
            value: None,
        })?;

        self.ofnat_uint16_inst_init = true;
        Ok(())
    }

    /// Check if OfNat UInt16 instance has been initialized
    pub(crate) fn has_ofnat_uint16(&self) -> bool {
        self.ofnat_uint16_inst_init
    }

    /// Initialize OfNat instance for UInt32
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ofnat_uint32_inst_init == true`
    /// ENSURES: On success, required dependencies (`ofnat`, `uint32`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_ofnat_uint32(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Fin-carrier / v4.8-shape carrier cluster (see init_uint8..64) —
        // suppressed in import mode so the genuine v4.31 declarations import.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.ofnat_uint32_inst_init {
            return Ok(());
        }

        self.init_ofnat()?;
        self.init_uint32()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let uint32_const = Expr::const_(Name::from_string("UInt32"), vec![]);
        let ofnat_const = Expr::const_(Name::from_string("OfNat"), vec![Level::zero()]);
        let ofnat_mk = Expr::const_(Name::from_string("OfNat.mk"), vec![Level::zero()]);
        let uint32_ofnat = Expr::const_(Name::from_string("UInt32.ofNat"), vec![]);

        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let e = Expr::app(
                Expr::app(ofnat_const.clone(), uint32_const.clone()),
                n.clone(),
            );
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(Expr::app(ofnat_mk.clone(), uint32_const.clone()), n.clone()),
                Expr::app(uint32_ofnat.clone(), n.clone()),
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        self.ensure_exact_checked_decl(Declaration::Definition {
            name: Name::from_string("instOfNatUInt32"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.ensure_exact_instance(KernelInstanceInfo {
            name: Name::from_string("instOfNatUInt32"),
            class_name: Name::from_string("OfNat"),
            priority: 100,
            type_: None,
            value: None,
        })?;

        self.ofnat_uint32_inst_init = true;
        Ok(())
    }

    /// Check if OfNat UInt32 instance has been initialized
    pub(crate) fn has_ofnat_uint32(&self) -> bool {
        self.ofnat_uint32_inst_init
    }

    /// Initialize OfNat instance for UInt64
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ofnat_uint64_inst_init == true`
    /// ENSURES: On success, required dependencies (`ofnat`, `uint64`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_ofnat_uint64(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Fin-carrier / v4.8-shape carrier cluster (see init_uint8..64) —
        // suppressed in import mode so the genuine v4.31 declarations import.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.ofnat_uint64_inst_init {
            return Ok(());
        }

        self.init_ofnat()?;
        self.init_uint64()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let uint64_const = Expr::const_(Name::from_string("UInt64"), vec![]);
        let ofnat_const = Expr::const_(Name::from_string("OfNat"), vec![Level::zero()]);
        let ofnat_mk = Expr::const_(Name::from_string("OfNat.mk"), vec![Level::zero()]);
        let uint64_ofnat = Expr::const_(Name::from_string("UInt64.ofNat"), vec![]);

        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let e = Expr::app(
                Expr::app(ofnat_const.clone(), uint64_const.clone()),
                n.clone(),
            );
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(Expr::app(ofnat_mk.clone(), uint64_const.clone()), n.clone()),
                Expr::app(uint64_ofnat.clone(), n.clone()),
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        self.ensure_exact_checked_decl(Declaration::Definition {
            name: Name::from_string("instOfNatUInt64"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.ensure_exact_instance(KernelInstanceInfo {
            name: Name::from_string("instOfNatUInt64"),
            class_name: Name::from_string("OfNat"),
            priority: 100,
            type_: None,
            value: None,
        })?;

        self.ofnat_uint64_inst_init = true;
        Ok(())
    }

    /// Check if OfNat UInt64 instance has been initialized
    pub(crate) fn has_ofnat_uint64(&self) -> bool {
        self.ofnat_uint64_inst_init
    }

    /// Initialize OfNat instance for USize
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ofnat_usize_inst_init == true`
    /// ENSURES: On success, required dependencies (`ofnat`, `usize`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_ofnat_usize(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Fin-carrier / v4.8-shape carrier cluster (see init_uint8..64) —
        // suppressed in import mode so the genuine v4.31 declarations import.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.ofnat_usize_inst_init {
            return Ok(());
        }

        self.init_ofnat()?;
        self.init_usize()?;

        // Genuine v4.30 USize is width-abstract, so `USize.ofNat` (which needs a
        // concrete `Fin.ofNat` form) is olean-supplied, not seeded. Without it
        // `instOfNatUSize` cannot be built natively — it too is olean-supplied.
        // Skip cleanly rather than fail prelude init (documented USize gap).
        if self.get_const(&Name::from_string("USize.ofNat")).is_none() {
            self.ofnat_usize_inst_init = true;
            return Ok(());
        }

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let usize_const = Expr::const_(Name::from_string("USize"), vec![]);
        let ofnat_const = Expr::const_(Name::from_string("OfNat"), vec![Level::zero()]);
        let ofnat_mk = Expr::const_(Name::from_string("OfNat.mk"), vec![Level::zero()]);
        let usize_ofnat = Expr::const_(Name::from_string("USize.ofNat"), vec![]);

        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let e = Expr::app(
                Expr::app(ofnat_const.clone(), usize_const.clone()),
                n.clone(),
            );
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(Expr::app(ofnat_mk.clone(), usize_const.clone()), n.clone()),
                Expr::app(usize_ofnat.clone(), n.clone()),
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        self.ensure_exact_checked_decl(Declaration::Definition {
            name: Name::from_string("instOfNatUSize"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.ensure_exact_instance(KernelInstanceInfo {
            name: Name::from_string("instOfNatUSize"),
            class_name: Name::from_string("OfNat"),
            priority: 100,
            type_: None,
            value: None,
        })?;

        self.ofnat_usize_inst_init = true;
        Ok(())
    }

    /// Check if OfNat USize instance has been initialized
    pub(crate) fn has_ofnat_usize(&self) -> bool {
        self.ofnat_usize_inst_init
    }
}

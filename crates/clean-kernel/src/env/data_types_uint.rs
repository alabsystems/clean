// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! UInt, Float, and USize type initialization for Environment

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY};
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl Environment {
    /// Shared helper for init_uint{8,16,32,64}/init_usize: creates the v4.30
    /// BitVec-backed carrier — the inductive `<Name>` with constructor
    /// `<Name>.ofBitVec : BitVec <width> → <Name>`, the `<Name>.toBitVec`
    /// projection, `.size`/`.toNat`/`.ofNat`/`.ofNatLT`. No `.mod` axiom, no
    /// `.toFin` (both olean-supplied under the genuine shape).
    ///
    /// GENUINE v4.30 FIDELITY (carrier = `BitVec <width>`):
    /// ```text
    /// abbrev UInt8.size : Nat := 256
    /// structure UInt8 where ofBitVec :: (toBitVec : BitVec 8)
    /// ```
    /// So `<Name>.ofBitVec : BitVec <width> → <Name>` and
    /// `<Name>.toBitVec : <Name> → BitVec <width>` — matching the real olean, so
    /// olean-imported UInt defs re-verify against the prelude.
    ///
    /// `width_e` is the OfNat-wrapped width literal (`8`/`16`/… or
    /// `System.Platform.numBits`); `size_value` is the `<Name>.size` body
    /// (`OfNat 256 …` or `2 ^ numBits`); `ofnat_fin_pred` is `Some(2^width - 1)`
    /// for concrete widths (enabling the `Fin.ofNat`-based `<Name>.ofNat`) or
    /// `None` (USize — width-abstract, `<Name>.ofNat` is olean-supplied).
    ///
    /// The caller checks/sets the init flag and runs `self.init_nat()`.
    fn init_uint_type(
        &mut self,
        name: &str,
        width_e: Expr,
        size_value: Expr,
        ofnat_fin_pred: Option<u64>,
    ) -> Result<(), EnvError> {
        // `BitVec` (carrier) + Pow/NatPow instances (its `2^w` index) first.
        self.init_pow_nat_instances()?;
        self.init_bitvec()?;

        let type_ = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
        let type_const = Expr::const_(Name::from_string(name), vec![]);
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let bitvec_const = Expr::const_(Name::from_string("BitVec"), vec![]);
        // The carrier `BitVec <width>`.
        let bitvec_w = Expr::app(bitvec_const.clone(), width_e.clone());

        // Add <Name>.size : Nat := <size_value>  (reducible def, matches abbrev).
        let size_name = format!("{name}.size");
        self.add_decl(Declaration::Definition {
            name: Name::from_string(&size_name),
            level_params: vec![],
            type_: nat_const.clone(),
            value: size_value,
            is_reducible: true,
        })?;
        let size_const = Expr::const_(Name::from_string(&size_name), vec![]);

        let ctor_name = format!("{name}.ofBitVec");
        // <Name>.ofBitVec : BitVec <width> → <Name>
        let ctor_type = Expr::pi(BinderInfo::Default, bitvec_w.clone(), type_const.clone());

        let decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(name),
                type_,
                constructors: vec![Constructor {
                    name: Name::from_string(&ctor_name),
                    type_: ctor_type,
                }],
            }],
        };
        self.add_inductive(decl)?;

        self.register_structure_fields(
            Name::from_string(name),
            vec![Name::from_string("toBitVec")],
        )?;

        // <Name>.toBitVec : <Name> → BitVec <width> := fun self => self.1  (Proj)
        let to_bitvec_name = format!("{name}.toBitVec");
        let to_bitvec_type = Expr::pi(BinderInfo::Default, type_const.clone(), bitvec_w.clone());
        let to_bitvec_value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(type_const.clone());
            let body = Expr::proj(Name::from_string(name), 0, x);
            let e = b.mk_lam(x_id, BinderInfo::Default, type_const.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(&to_bitvec_name),
            level_params: vec![],
            type_: to_bitvec_type,
            value: to_bitvec_value,
            is_reducible: true,
        })?;

        let to_bitvec_const = Expr::const_(Name::from_string(&to_bitvec_name), vec![]);
        let bitvec_to_nat = Expr::const_(Name::from_string("BitVec.toNat"), vec![]);
        let bitvec_offin = Expr::const_(Name::from_string("BitVec.ofFin"), vec![]);
        let bitvec_ofnatlt = Expr::const_(Name::from_string("BitVec.ofNatLT"), vec![]);
        let fin_ofnat = Expr::const_(Name::from_string("Fin.ofNat"), vec![]);
        let ctor_const = Expr::const_(Name::from_string(&ctor_name), vec![]);

        // <Name>.toNat : <Name> → Nat := fun n => @BitVec.toNat <width> (<Name>.toBitVec n)
        let to_nat_name = format!("{name}.toNat");
        let to_nat_type = Expr::pi(BinderInfo::Default, type_const.clone(), nat_const.clone());
        let to_nat_value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(type_const.clone());
            let body = Expr::apps(
                bitvec_to_nat.clone(),
                [width_e.clone(), Expr::app(to_bitvec_const.clone(), x)],
            );
            let e = b.mk_lam(x_id, BinderInfo::Default, type_const.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string(&to_nat_name),
            level_params: vec![],
            type_: to_nat_type,
            value: to_nat_value,
            is_reducible: true,
        })?;

        // <Name>.ofNat : Nat → <Name> (concrete widths only).
        //   := fun n => <Name>.ofBitVec (@BitVec.ofFin <width> (@Fin.ofNat (2^w-1) n))
        // `Fin.ofNat (2^w-1) n : Fin (succ (2^w-1)) ≡ Fin (2^w)`, so it inhabits
        // `BitVec.ofFin`'s `Fin (2^width)` field; value-def-eq to the oracle's
        // `<Name>.ofBitVec (BitVec.ofNat width n)` (both reduce to
        // `BitVec.ofFin width (Fin.mk (2^w) (n % 2^w) _)`).
        if let Some(pred) = ofnat_fin_pred {
            let of_nat_name = format!("{name}.ofNat");
            let of_nat_type = Expr::pi(BinderInfo::Default, nat_const.clone(), type_const.clone());
            let of_nat_value = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat_const.clone());
                let fin_of = Expr::apps(fin_ofnat.clone(), [Expr::nat_lit(pred), n]);
                let bv = Expr::apps(bitvec_offin.clone(), [width_e.clone(), fin_of]);
                let body = Expr::app(ctor_const.clone(), bv);
                let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&of_nat_name),
                level_params: vec![],
                type_: of_nat_type,
                value: of_nat_value,
                is_reducible: true,
            })?;
        }

        // <Name>.ofNatLT : (n : Nat) → (h : n < <Name>.size) → <Name>
        //   := fun n h => <Name>.ofBitVec (@BitVec.ofNatLT <width> n h)
        // `<Name>.size ≡ 2^width`, so `h : n < <Name>.size` is `BitVec.ofNatLT`'s
        // `n < 2^width` bound by def-eq.
        {
            let inst_lt_nat = Expr::const_(Name::from_string("instLTNat"), vec![]);
            let lt = |l: Expr, r: Expr| {
                Expr::apps(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    [nat_const.clone(), inst_lt_nat.clone(), l, r],
                )
            };
            let of_nat_lt_name = format!("{name}.ofNatLT");
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat_const.clone());
                let h_ty = lt(n.clone(), size_const.clone());
                let (h_id, _) = b.fresh_local(h_ty.clone());
                let r = b.mk_pi(h_id, BinderInfo::Default, h_ty, type_const.clone());
                let r = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), r);
                b.finish(r)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat_const.clone());
                let h_ty = lt(n.clone(), size_const.clone());
                let (h_id, h) = b.fresh_local(h_ty.clone());
                let bv = Expr::apps(bitvec_ofnatlt.clone(), [width_e.clone(), n.clone(), h]);
                let body = Expr::app(ctor_const.clone(), bv);
                let r = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
                let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(&of_nat_lt_name),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: true,
            })?;
        }

        Ok(())
    }

    /// Initialize UInt8 type
    ///
    /// UInt8 is a structure wrapping a natural number in [0, 256).
    /// In Lean 4, it wraps Fin UInt8.size. Here we simplify to wrap Nat.
    ///
    /// structure UInt8 where
    ///   val : Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.uint8_init == true`
    /// ENSURES: On success, required dependencies (`nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_uint8(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): the Fin-carrier UInt shape is Lean v4.8 fidelity —
        // genuine v4.31 UInts wrap `BitVec w` (ctor `ofBitVec`), and the
        // `UInt<w>.ofNat` values here reference the v4.8-signature
        // `Fin.ofNat` which is itself import-suppressed. Skip the cluster in
        // import mode so the genuine v4.31 BitVec-based carriers import
        // through the checked path (the default lane keeps the v4.8 shapes;
        // the BitVec reshape of the default lane is the carrier-parity
        // track, designs/2026-07-03-carrier-types-bitvec-parity.md).
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.uint8_init {
            return Ok(());
        }
        self.init_nat()?;
        // UInt8: carrier BitVec 8, size 256, Fin.ofNat pred 255.
        self.init_uint_type(
            "UInt8",
            Self::ofnat_nat_lit(8),
            Expr::nat_lit(256),
            Some(255),
        )?;
        self.uint8_init = true;
        Ok(())
    }

    /// Check if UInt8 has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_uint8` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_uint8(&self) -> bool {
        self.uint8_init
    }

    /// Initialize UInt16 type
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.uint16_init == true`
    /// ENSURES: On success, required dependencies (`nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_uint16(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): the Fin-carrier UInt shape is Lean v4.8 fidelity —
        // genuine v4.31 UInts wrap `BitVec w` (ctor `ofBitVec`), and the
        // `UInt<w>.ofNat` values here reference the v4.8-signature
        // `Fin.ofNat` which is itself import-suppressed. Skip the cluster in
        // import mode so the genuine v4.31 BitVec-based carriers import
        // through the checked path (the default lane keeps the v4.8 shapes;
        // the BitVec reshape of the default lane is the carrier-parity
        // track, designs/2026-07-03-carrier-types-bitvec-parity.md).
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.uint16_init {
            return Ok(());
        }
        self.init_nat()?;
        // UInt16: carrier BitVec 16, size 65536, Fin.ofNat pred 65535.
        self.init_uint_type(
            "UInt16",
            Self::ofnat_nat_lit(16),
            Expr::nat_lit(65536),
            Some(65535),
        )?;
        self.uint16_init = true;
        Ok(())
    }

    /// Check if UInt16 has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_uint16` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_uint16(&self) -> bool {
        self.uint16_init
    }

    /// Initialize UInt32 type
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.uint32_init == true`
    /// ENSURES: On success, required dependencies (`nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_uint32(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): the Fin-carrier UInt shape is Lean v4.8 fidelity —
        // genuine v4.31 UInts wrap `BitVec w` (ctor `ofBitVec`), and the
        // `UInt<w>.ofNat` values here reference the v4.8-signature
        // `Fin.ofNat` which is itself import-suppressed. Skip the cluster in
        // import mode so the genuine v4.31 BitVec-based carriers import
        // through the checked path (the default lane keeps the v4.8 shapes;
        // the BitVec reshape of the default lane is the carrier-parity
        // track, designs/2026-07-03-carrier-types-bitvec-parity.md).
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.uint32_init {
            return Ok(());
        }
        self.init_nat()?;
        // UInt32: carrier BitVec 32, size 2^32, Fin.ofNat pred 2^32-1.
        self.init_uint_type(
            "UInt32",
            Self::ofnat_nat_lit(32),
            Expr::nat_lit(4294967296),
            Some(4294967295),
        )?;
        self.uint32_init = true;
        Ok(())
    }

    /// Check if UInt32 has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_uint32` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_uint32(&self) -> bool {
        self.uint32_init
    }

    /// Initialize UInt64 type
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.uint64_init == true`
    /// ENSURES: On success, required dependencies (`nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_uint64(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): the Fin-carrier UInt shape is Lean v4.8 fidelity —
        // genuine v4.31 UInts wrap `BitVec w` (ctor `ofBitVec`), and the
        // `UInt<w>.ofNat` values here reference the v4.8-signature
        // `Fin.ofNat` which is itself import-suppressed. Skip the cluster in
        // import mode so the genuine v4.31 BitVec-based carriers import
        // through the checked path (the default lane keeps the v4.8 shapes;
        // the BitVec reshape of the default lane is the carrier-parity
        // track, designs/2026-07-03-carrier-types-bitvec-parity.md).
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.uint64_init {
            return Ok(());
        }
        self.init_nat()?;
        // UInt64: carrier BitVec 64, size 2^64 (> u64::MAX, u128), Fin.ofNat
        // pred = 2^64 - 1 = u64::MAX.
        self.init_uint_type(
            "UInt64",
            Self::ofnat_nat_lit(64),
            Expr::nat_lit_u128(1u128 << 64),
            Some(u64::MAX),
        )?;
        self.uint64_init = true;
        Ok(())
    }

    /// Check if UInt64 has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_uint64` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_uint64(&self) -> bool {
        self.uint64_init
    }

    /// Initialize Float type
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.float_init == true`
    /// ENSURES: On success, required dependencies (`nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_float(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Float's toUInt8/16/32/64 companions reference the import-suppressed
        // Fin-carrier UInt ops (see init_uint8..64 above). Suppressed with
        // them; the genuine v4.31 Float cluster imports instead.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.float_init {
            return Ok(());
        }
        self.init_nat()?;

        let float_type = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
        let float_const = Expr::const_(Name::from_string("Float"), vec![]);
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);

        let float_mk_type = Expr::pi(BinderInfo::Default, nat_const.clone(), float_const.clone());

        let float_decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("Float"),
                type_: float_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Float.mk"),
                    type_: float_mk_type,
                }],
            }],
        };
        self.add_inductive(float_decl)?;

        self.structure_fields
            .insert(Name::from_string("Float"), vec![Name::from_string("val")]);

        // Add `Float.val : Float → Nat` — the projection to the underlying bit
        // pattern. `Float.val (Float.mk n)` ι-reduces to `n`, which lets the
        // native `Float.decEq` reducer build a sound *structural* (bitwise)
        // disproof via `congrArg Float.val` + `Nat.ne_of_beq_false`. (Mirrors the
        // `<UIntN>.val` projections built by `init_uint_type`.)
        let val_type = Expr::pi(BinderInfo::Default, float_const.clone(), nat_const.clone());
        let rec_const = Expr::const_(
            Name::from_string("Float.rec"),
            vec![Level::succ(Level::zero())],
        );
        let motive = Expr::lam(BinderInfo::Default, float_const.clone(), nat_const.clone());
        let val_value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(float_const.clone());
            let (v_id, v) = b.fresh_local(nat_const.clone());
            let minor = b.mk_lam(v_id, BinderInfo::Default, nat_const.clone(), v);
            let body = Expr::apps(rec_const, [motive, minor, x]);
            let e = b.mk_lam(x_id, BinderInfo::Default, float_const.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Float.val"),
            level_params: vec![],
            type_: val_type,
            value: val_value,
            is_reducible: true,
        })?;

        self.float_init = true;
        Ok(())
    }

    /// Check if Float has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_float` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_float(&self) -> bool {
        self.float_init
    }

    /// Initialize all UInt types at once
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `uint8_init`, `uint16_init`, `uint32_init`, `uint64_init` are all `true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_uint_types(&mut self) -> Result<(), EnvError> {
        self.init_uint8()?;
        self.init_uint16()?;
        self.init_uint32()?;
        self.init_uint64()?;
        Ok(())
    }

    /// Trust: wrapping machine arithmetic for one UInt type — `<Name>.add`,
    /// `.sub`, `.mul` over the BitVec-backed carrier, defined THROUGH the
    /// existing `.toNat` (carrier → Nat) and `.ofNat` (Nat → carrier, which
    /// wraps mod 2^w via `Fin.ofNat`), so no new arithmetic axioms are
    /// introduced and every op is kernel-checked at registration:
    ///
    /// ```text
    /// <Name>.add a b := <Name>.ofNat (Nat.add a.toNat b.toNat)   -- wraps
    /// <Name>.sub a b := <Name>.ofNat (Nat.add a.toNat (Nat.sub <Name>.size b.toNat))
    /// <Name>.mul a b := <Name>.ofNat (Nat.mul a.toNat b.toNat)   -- wraps
    /// ```
    ///
    /// `sub` uses the two's-complement identity `a - b ≡ a + (2^w - b)` so it
    /// stays inside `Nat` (no `Nat.sub` truncation surprise on the result),
    /// then `.ofNat` reduces mod `<Name>.size = 2^w`. This is the machine
    /// (wrapping) semantics the design's §1.1 domain-tagged arithmetic
    /// requires for `u32`/`u64` clauses — distinct from `Nat`/`Int`.
    ///
    /// The caller (`init_uint_arith`) requires a concrete-width `<Name>` already
    /// initialized (its `.toNat`/`.ofNat`/`.size`) plus `init_nat`. `USize` is
    /// deliberately excluded: its width is platform-abstract and the native
    /// prelude has no canonical `USize.ofNat` to ground these definitions.
    fn init_one_uint_arith(&mut self, name: &str) -> Result<(), EnvError> {
        let ty = Expr::const_(Name::from_string(name), vec![]);
        let to_nat = Expr::const_(Name::from_string(&format!("{name}.toNat")), vec![]);
        let of_nat = Expr::const_(Name::from_string(&format!("{name}.ofNat")), vec![]);
        let size = Expr::const_(Name::from_string(&format!("{name}.size")), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);

        // Build `fun (a b : <Name>) => <Name>.ofNat (<combine> a.toNat b.toNat)`.
        let mk_binop = |combine: &dyn Fn(Expr, Expr) -> Expr| {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(ty.clone());
            let (bb_id, bb) = b.fresh_local(ty.clone());
            let a_nat = Expr::app(to_nat.clone(), a);
            let b_nat = Expr::app(to_nat.clone(), bb);
            let body = Expr::app(of_nat.clone(), combine(a_nat, b_nat));
            let inner = b.mk_lam(bb_id, BinderInfo::Default, ty.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, ty.clone(), inner);
            b.finish(e)
        };
        let binop_ty = {
            let mut b = EnvDeclBuilder::new();
            let (bb_id, _) = b.fresh_local(ty.clone());
            let inner = b.mk_pi(bb_id, BinderInfo::Default, ty.clone(), ty.clone());
            let (a_id, _) = b.fresh_local(ty.clone());
            let r = b.mk_pi(a_id, BinderInfo::Default, ty.clone(), inner);
            b.finish(r)
        };

        let nat_add_c = nat_add.clone();
        let add_val = mk_binop(&|x, y| Expr::apps(nat_add_c.clone(), [x, y]));
        let sub_val = mk_binop(&|x, y| {
            // x + (size - y) — two's-complement wrap, stays in Nat.
            let comp = Expr::apps(nat_sub.clone(), [size.clone(), y]);
            Expr::apps(nat_add.clone(), [x, comp])
        });
        let nat_mul_c = nat_mul.clone();
        let mul_val = mk_binop(&|x, y| Expr::apps(nat_mul_c.clone(), [x, y]));

        for (op, value) in [("add", add_val), ("sub", sub_val), ("mul", mul_val)] {
            self.ensure_exact_checked_decl(Declaration::Definition {
                name: Name::from_string(&format!("{name}.{op}")),
                level_params: vec![],
                type_: binop_ty.clone(),
                value,
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    /// Trust: wrapping machine arithmetic + `HAdd`/`HSub`/`HMul` instances for
    /// every concrete fixed-width UInt (`UInt8/16/32/64`, two-language design
    /// §1.1). After this,
    /// `x + 1 : UInt64` and friends elaborate against the single-file prelude,
    /// so the spec elaborator can target machine-typed goals. `USize` remains
    /// intentionally unavailable until a platform-width-bound `USize.ofNat`
    /// exists; claiming portable wrap semantics without that binding would be
    /// unsound. Idempotent and retry-safe after any partially completed call.
    pub fn init_uint_arith(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE: the UInt carrier family is deliberately withheld so the
        // genuine Lean declarations can enter through checked import. Arithmetic
        // is one indivisible overlay over those carriers: attempting to build it
        // after `init_uint_types` has correctly no-op'd produces declarations
        // whose types mention missing `UInt8`/`UInt16`/`UInt32`/`UInt64` heads.
        // Guard the public initializer itself so every caller is fail-safe, not
        // only the current prelude call site.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.init_nat()?;
        self.init_uint_types()?;
        self.init_hadd()?;
        self.init_hsub()?;
        self.init_hmul()?;
        // Arithmetic literals (`x + 1`) require the OfNat resolver entry for
        // the actual carrier width, not merely the UInt64 instance.
        self.init_ofnat_uint8()?;
        self.init_ofnat_uint16()?;
        self.init_ofnat_uint32()?;
        self.init_ofnat_uint64()?;

        for name in ["UInt8", "UInt16", "UInt32", "UInt64"] {
            self.init_one_uint_arith(name)?;
            for (class, ctor, op) in [
                ("HAdd", "HAdd.mk", "add"),
                ("HSub", "HSub.mk", "sub"),
                ("HMul", "HMul.mk", "mul"),
            ] {
                let inst_name = format!("inst{class}{name}");
                self.add_homogeneous_hetero_instance(
                    &inst_name,
                    class,
                    ctor,
                    name,
                    &format!("{name}.{op}"),
                )?;
                // Register with the instance resolver so `x + y : <Name>`
                // synthesizes the instance (the definition alone is not
                // enough — the OfNat/Nat lanes register the same way).
                let instance = KernelInstanceInfo {
                    name: Name::from_string(&inst_name),
                    class_name: Name::from_string(class),
                    priority: DEFAULT_INSTANCE_PRIORITY,
                    type_: None,
                    value: None,
                };
                self.ensure_exact_instance(instance)?;
            }
        }
        Ok(())
    }

    /// Seed the genuine v4.30 width-abstract platform model:
    /// `System.Platform.getNumBits : Unit → {n // n = 32 ∨ n = 64}` (OPAQUE —
    /// irreducible, so width facts are undecidable in the kernel exactly as in
    /// Lean) and `System.Platform.numBits := (getNumBits ()).val`.
    fn register_platform_num_bits(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("System.Platform.numBits"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nat()?;
        self.init_ofnat_nat()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let unit = Expr::const_(Name::from_string("Unit"), vec![]);
        let of32 = Self::ofnat_nat_lit(32);
        let of64 = Self::ofnat_nat_lit(64);
        let eq_nat = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [nat.clone(), l, r],
            )
        };
        let or =
            |a: Expr, b: Expr| Expr::apps(Expr::const_(Name::from_string("Or"), vec![]), [a, b]);
        // P := fun (n : Nat) => Or (Eq Nat n 32) (Eq Nat n 64)
        let pred = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let body = or(
                eq_nat(n.clone(), of32.clone()),
                eq_nat(n.clone(), of64.clone()),
            );
            b.finish(b.mk_lam(n_id, BinderInfo::Default, nat.clone(), body))
        };
        let subtype = Expr::apps(
            Expr::const_(
                Name::from_string("Subtype"),
                vec![Level::succ(Level::zero())],
            ),
            [nat.clone(), pred.clone()],
        );

        // getNumBits : Unit → Subtype Nat P  (OPAQUE)
        let get_num_bits_type = Expr::pi(BinderInfo::Default, unit.clone(), subtype.clone());
        // hidden witness: fun _ => @Subtype.mk Nat P 64 (Or.inr rfl)
        let get_num_bits_value = {
            let mut b = EnvDeclBuilder::new();
            let (u_id, _u) = b.fresh_local(unit.clone());
            let proof = Expr::apps(
                Expr::const_(Name::from_string("Or.inr"), vec![]),
                [
                    eq_nat(of64.clone(), of32.clone()),
                    eq_nat(of64.clone(), of64.clone()),
                    Expr::apps(
                        Expr::const_(
                            Name::from_string("Eq.refl"),
                            vec![Level::succ(Level::zero())],
                        ),
                        [nat.clone(), of64.clone()],
                    ),
                ],
            );
            let mk = Expr::apps(
                Expr::const_(
                    Name::from_string("Subtype.mk"),
                    vec![Level::succ(Level::zero())],
                ),
                [nat.clone(), pred.clone(), of64.clone(), proof],
            );
            b.finish(b.mk_lam(u_id, BinderInfo::Default, unit.clone(), mk))
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("System.Platform.getNumBits"),
            level_params: vec![],
            type_: get_num_bits_type,
            value: get_num_bits_value,
        })?;

        // numBits : Nat := @Subtype.val Nat P (getNumBits Unit.unit)
        let num_bits_value = {
            let get = Expr::app(
                Expr::const_(Name::from_string("System.Platform.getNumBits"), vec![]),
                Expr::const_(Name::from_string("Unit.unit"), vec![]),
            );
            Expr::apps(
                Expr::const_(
                    Name::from_string("Subtype.val"),
                    vec![Level::succ(Level::zero())],
                ),
                [nat.clone(), pred, get],
            )
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("System.Platform.numBits"),
            level_params: vec![],
            type_: nat,
            value: num_bits_value,
            is_reducible: false,
        })?;
        Ok(())
    }

    /// Initialize USize — genuine v4.30 width-ABSTRACT carrier
    /// `BitVec System.Platform.numBits` (§1.5). `numBits` is opaque, so
    /// width-dependent USize facts are undecidable in the kernel, matching Lean
    /// exactly (Clean's old `USize.size := 2^64` shortcut was a def-eq excess).
    /// `USize.ofNat`/`instOfNatUSize` are olean-supplied (symbolic width has no
    /// concrete `Fin.ofNat` form) — a documented native-lane USize gap.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.usize_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_usize(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // Fin-carrier / v4.8-shape carrier cluster (see init_uint8..64) —
        // suppressed in import mode so the genuine v4.31 declarations import.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.usize_init {
            return Ok(());
        }
        self.init_nat()?;
        self.init_pow_nat_instances()?;
        self.init_bitvec()?;
        self.register_platform_num_bits()?;
        let numbits = Expr::const_(Name::from_string("System.Platform.numBits"), vec![]);
        // USize.size := 2 ^ numBits  (abstract); carrier BitVec numBits.
        self.init_uint_type("USize", numbits.clone(), Self::two_pow(numbits), None)?;
        self.usize_init = true;
        Ok(())
    }

    /// Check if USize has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_usize` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_usize(&self) -> bool {
        self.usize_init
    }

    /// Register `USize.ofNat : Nat → USize` as a genuine kernel-checked def.
    ///
    /// `USize` wraps `BitVec System.Platform.numBits` — a WIDTH-ABSTRACT carrier
    /// (`numBits` is opaque), so the concrete-width `Fin.ofNat (2^w - 1)` path that
    /// builds `UInt8.ofNat`/…/`UInt64.ofNat` in `init_uint_type` cannot apply
    /// (there is no concrete `2^numBits - 1`). The numeric-literal elaborator still
    /// lowers `(n : USize)` to `USize.ofNat n` (see
    /// `clean-elab/src/infer/coercion.rs`), so without the constant `def u : USize
    /// := 42` failed the kernel check with `Unknown constant: USize.ofNat`
    /// (GAP_SWEEP literals/p17).
    ///
    /// Lean 4 defines `USize.ofNat n := ⟨BitVec.ofNat numBits n⟩`. Here the
    /// equivalent kernel-checked body is
    /// `USize.ofNatLT (n % USize.size) (Nat.mod_lt n USize.size h)`, where
    /// `h : 0 < USize.size` (= `0 < 2 ^ numBits`, def-eq `USize.size`) is the
    /// verified positivity witness `Nat.pow_le_pow_right 2 0 numBits (1 ≤ 2)
    /// (0 ≤ numBits)` — the exact construction the kernel-checked
    /// `Nat.one_le_two_pow` uses (`boolean_analysis_expect_one_proof.rs`). NO new
    /// axiom, NO `sorry`, NO `add_decl_unchecked`: the whole term is re-checked by
    /// `add_decl`.
    ///
    /// `USize.ofNat` is registered `is_reducible: false` — the abstract `numBits`
    /// leaves `n % 2 ^ numBits` irreducible, so a value pin like
    /// `(USize.ofNat 42).toNat = 42 := rfl` honestly does NOT reduce (matching
    /// Lean, whose `numBits` is likewise opaque in the kernel — an honest loud
    /// gap, never a silently-accepted wrong value).
    ///
    /// Import mode (`suppress_lossy_structure_stubs`) skips this: `init_usize` is
    /// itself suppressed there and the genuine olean-supplied `USize.ofNat`
    /// imports through the checked path.
    pub(crate) fn register_usize_of_nat(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.get_const(&Name::from_string("USize.ofNat")).is_some() {
            return Ok(());
        }
        // Dependencies (all idempotent, self-seeding): the USize carrier
        // (`USize.size`/`USize.ofNatLT`), the modulus bound `Nat.mod_lt`, and the
        // pow-monotonicity lemma `Nat.pow_le_pow_right` used for positivity.
        self.init_usize()?;
        self.init_nat_div_mod_lemmas()?;
        self.register_nat_pow_le_pow_right_proof()?;

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let usize_c = Expr::const_(Name::from_string("USize"), vec![]);
        let usize_size = Expr::const_(Name::from_string("USize.size"), vec![]);
        let numbits = Expr::const_(Name::from_string("System.Platform.numBits"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let one = Expr::app(nat_succ.clone(), nat_zero.clone());
        let two = Expr::app(nat_succ.clone(), one.clone());

        // hpos : Nat.le (Nat.pow 2 0) (Nat.pow 2 numBits)
        //      ≡ Nat.le 1 (2 ^ numBits) ≡ Nat.lt 0 USize.size  (all def-eq).
        // Mirrors `one_le_two_pow_value` (boolean_analysis_expect_one_proof.rs):
        //   h12       := Nat.le.step 1 1 (Nat.le.refl 1)   : Nat.le 1 2
        //   zero_le_n := Nat.zero_le numBits               : Nat.le 0 numBits
        //   hpos      := Nat.pow_le_pow_right 2 0 numBits h12 zero_le_n.
        let le_refl_1 = Expr::app(
            Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
            one.clone(),
        );
        let h12 = Expr::apps(
            Expr::const_(Name::from_string("Nat.le.step"), vec![]),
            [one.clone(), one.clone(), le_refl_1],
        );
        let zero_le_nb = Expr::app(
            Expr::const_(Name::from_string("Nat.zero_le"), vec![]),
            numbits.clone(),
        );
        let hpos = Expr::apps(
            Expr::const_(Name::from_string("Nat.pow_le_pow_right"), vec![]),
            [two, nat_zero, numbits, h12, zero_le_nb],
        );

        let of_nat_ty = Expr::pi(BinderInfo::Default, nat.clone(), usize_c);

        // fun (n : Nat) => USize.ofNatLT (Nat.mod n USize.size)
        //                                (Nat.mod_lt n USize.size hpos)
        let of_nat_val = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let modv = Expr::apps(
                Expr::const_(Name::from_string("Nat.mod"), vec![]),
                [n.clone(), usize_size.clone()],
            );
            let modlt = Expr::apps(
                Expr::const_(Name::from_string("Nat.mod_lt"), vec![]),
                [n.clone(), usize_size.clone(), hpos],
            );
            let body = Expr::apps(
                Expr::const_(Name::from_string("USize.ofNatLT"), vec![]),
                [modv, modlt],
            );
            let e = b.mk_lam(n_id, BinderInfo::Default, nat, body);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("USize.ofNat"),
            level_params: vec![],
            type_: of_nat_ty,
            value: of_nat_val,
            is_reducible: false,
        })?;
        Ok(())
    }
}

#[cfg(test)]
mod carrier_fidelity_tests {
    //! Genuine v4.30 carrier fidelity for the fixed-width UInt widths:
    //! `structure UInt<w> where ofBitVec :: (toBitVec : BitVec <w>)` — i.e.
    //! `UInt<w>.ofBitVec : BitVec <w> → UInt<w>` and
    //! `UInt<w>.toBitVec : UInt<w> → BitVec <w>`. (P1 reshape; the old Fin
    //! carrier is REJECTED — adversarial pins below.)
    use super::*;
    use crate::tc::TypeChecker;

    // (name, size, width) for the fixed widths.
    const WIDTHS: &[(&str, u64, u64)] = &[
        ("UInt8", 256, 8),
        ("UInt16", 65536, 16),
        ("UInt32", 4294967296, 32),
    ];

    fn is_const(e: &Expr, name: &str) -> bool {
        matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == name)
    }

    /// `UInt<w>.size` is a reducible `Definition` equal to the literal `2^w`.
    #[test]
    fn test_uint_size_is_literal_def() {
        let env = Environment::with_prelude();
        for &(name, size, _) in WIDTHS {
            let info = env
                .get_const(&Name::from_string(&format!("{name}.size")))
                .unwrap_or_else(|| panic!("{name}.size must be registered"));
            let val = info
                .value
                .as_ref()
                .unwrap_or_else(|| panic!("{name}.size must be a def with a value"));
            match val.kind() {
                ExprKind::Lit(crate::expr::Literal::Nat(n)) => {
                    assert_eq!(n.to_u64(), Some(size), "{name}.size must be {size}");
                }
                other => panic!("{name}.size value must be a Nat literal, got {other:?}"),
            }
        }
    }

    /// FIDELITY: `UInt<w>.ofBitVec`'s constructor argument type is `BitVec <w>`
    /// (NOT `Fin _`), and `UInt<w>.toBitVec`'s result type is `BitVec <w>`.
    #[test]
    fn test_uint_carrier_is_bitvec() {
        let env = Environment::with_prelude();
        for &(name, _, _) in WIDTHS {
            let ctor = env
                .get_constructor(&Name::from_string(&format!("{name}.ofBitVec")))
                .unwrap_or_else(|| panic!("{name}.ofBitVec must be a constructor"));
            let ExprKind::Pi(_, arg_ty, _) = ctor.type_.kind() else {
                panic!("{name}.ofBitVec must be a Pi (field -> struct)");
            };
            assert!(
                is_const(arg_ty.get_app_fn(), "BitVec"),
                "{name}.ofBitVec field type must be `BitVec _`, got head {:?}",
                arg_ty.get_app_fn()
            );
            // <name>.toBitVec : <name> -> BitVec <w>
            let proj = env
                .get_const(&Name::from_string(&format!("{name}.toBitVec")))
                .unwrap_or_else(|| panic!("{name}.toBitVec must be registered"));
            let ExprKind::Pi(_, _, res_ty) = proj.type_.kind() else {
                panic!("{name}.toBitVec must be a Pi");
            };
            assert!(
                is_const(res_ty.get_app_fn(), "BitVec"),
                "{name}.toBitVec result must be `BitVec _`, got head {:?}",
                res_ty.get_app_fn()
            );
        }
    }

    /// USE-SITE: `UInt8.ofNat 5` type-checks at `UInt8`.
    #[test]
    fn test_uint8_ofnat_use_site_type_checks() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let of = Expr::app(
            Expr::const_(Name::from_string("UInt8.ofNat"), vec![]),
            Expr::nat_lit(5),
        );
        let inferred = tc.infer_type(&of).expect("UInt8.ofNat 5 must type-check");
        assert!(is_const(&inferred, "UInt8"), "got {inferred:?}");
    }

    /// ADVERSARIAL: the OLD Fin-carrier ctor `UInt8.mk` no longer exists, and
    /// `UInt8.ofBitVec` applied to a bare `Nat`/`Fin` is REJECTED (its field is
    /// `BitVec 8`, genuinely not def-eq to `Nat` or `Fin _`).
    #[test]
    fn test_old_fin_carrier_is_rejected() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        assert!(
            env.get_const(&Name::from_string("UInt8.mk")).is_none(),
            "UInt8.mk (old Fin-carrier ctor) must NOT exist under the BitVec carrier"
        );
        // `UInt8.ofBitVec 5` (bare Nat into the BitVec field) must be rejected.
        let bad = Expr::app(
            Expr::const_(Name::from_string("UInt8.ofBitVec"), vec![]),
            Expr::nat_lit(5),
        );
        let uint8 = Expr::const_(Name::from_string("UInt8"), vec![]);
        assert!(
            tc.check_type(&bad, &uint8).is_err(),
            "UInt8.ofBitVec on a bare Nat must be REJECTED (field is BitVec 8)"
        );
    }

    /// `UInt8.toNat`/`ofNat`/`toBitVec` are axiom-free reducible defs; the
    /// `<T>.mod` axioms are DELETED and `<T>.toFin` is not seeded.
    #[test]
    fn test_uint8_defs_axiom_free_and_mod_deleted() {
        let env = Environment::with_prelude();
        for cname in [
            "UInt8.toNat",
            "UInt8.ofNat",
            "UInt8.toBitVec",
            "UInt8.ofNatLT",
        ] {
            let deps = env
                .axiom_deps(&Name::from_string(cname))
                .unwrap_or_else(|| panic!("{cname} must be registered"));
            let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                names.is_empty(),
                "{cname} must be axiom-free, got {names:?}"
            );
        }
        for w in ["UInt8", "UInt16", "UInt32", "UInt64", "USize"] {
            assert!(
                env.get_const(&Name::from_string(&format!("{w}.mod")))
                    .is_none(),
                "{w}.mod axiom must be DELETED (P1)"
            );
        }
    }

    fn uint8(n: u64) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("UInt8.ofNat"), vec![]),
            Expr::nat_lit(n),
        )
    }

    fn uint8_binop(op: &str, a: u64, b: u64) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string(&format!("UInt8.{op}")), vec![]),
            [uint8(a), uint8(b)],
        )
    }

    /// The definitions are not merely present: their kernel reduction has the
    /// expected modulo-256 semantics at all three wrap boundaries.
    #[test]
    fn test_uint8_arithmetic_wraps_add_sub_mul() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for (actual, expected, label) in [
            (uint8_binop("add", 255, 1), uint8(0), "255 + 1"),
            (uint8_binop("sub", 0, 1), uint8(255), "0 - 1"),
            (uint8_binop("mul", 16, 16), uint8(0), "16 * 16"),
        ] {
            assert!(
                tc.is_def_eq(&actual, &expected),
                "UInt8 {label} must reduce with modulo-256 semantics"
            );
        }
    }

    /// Retry after an intentionally half-completed first width. The exact
    /// declaration gate must resume rather than duplicate/fail, and repeated
    /// complete calls must not duplicate resolver entries.
    #[test]
    fn test_uint_arith_partial_resume_and_idempotence() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_uint_types().expect("UInt carriers");
        env.init_one_uint_arith("UInt8")
            .expect("simulate first completed arithmetic slice");

        env.init_uint_arith().expect("resume partial initializer");
        env.init_uint_arith().expect("fully idempotent retry");

        for width in ["UInt8", "UInt16", "UInt32", "UInt64"] {
            let of_nat = Name::from_string(&format!("instOfNat{width}"));
            let of_nat_occurrences = env
                .get_class_instances(&Name::from_string("OfNat"))
                .iter()
                .filter(|entry| entry.name == of_nat)
                .count();
            assert_eq!(
                of_nat_occurrences, 1,
                "{of_nat} must be registered exactly once"
            );

            for (class, op) in [("HAdd", "add"), ("HSub", "sub"), ("HMul", "mul")] {
                assert!(
                    env.get_const(&Name::from_string(&format!("{width}.{op}")))
                        .is_some(),
                    "missing {width}.{op} after resume"
                );
                let instance = Name::from_string(&format!("inst{class}{width}"));
                let occurrences = env
                    .get_class_instances(&Name::from_string(class))
                    .iter()
                    .filter(|entry| entry.name == instance)
                    .count();
                assert_eq!(occurrences, 1, "{instance} must be registered exactly once");
            }
        }
    }

    /// A same-name declaration with altered reduction authority is not an
    /// idempotent hit. The initializer compares the full `Reducibility`, not
    /// only the legacy `is_reducible` boolean.
    #[test]
    fn test_uint_arith_rejects_reducibility_squatting() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_uint_types().expect("UInt carriers");
        env.init_one_uint_arith("UInt8").expect("UInt8 arithmetic");
        let add = Name::from_string("UInt8.add");
        assert!(env.set_reducibility(&add, crate::env::Reducibility::Irreducible));
        let error = env
            .init_uint_arith()
            .expect_err("altered reducibility must not count as initialized");
        assert!(
            matches!(error, EnvError::InitializationConflict { ref name, .. } if *name == add),
            "unexpected error: {error:?}"
        );
    }

    #[test]
    fn test_uint_arith_rejects_unsafe_or_partial_existing_payload() {
        for partial in [false, true] {
            let mut env = Environment::new();
            env.init_nat().expect("Nat");
            env.init_uint_types().expect("UInt carriers");
            env.init_one_uint_arith("UInt8").expect("UInt8 arithmetic");
            let add = Name::from_string("UInt8.add");
            if partial {
                env.mark_partial(add.clone());
            } else {
                env.mark_unsafe(add.clone());
            }
            let error = env
                .init_uint_arith()
                .expect_err("unsafe/partial existing payload must not be restamped");
            assert!(
                matches!(error, EnvError::InitializationConflict { ref name, .. } if *name == add),
                "unexpected error: {error:?}"
            );
        }
    }

    /// USize is platform-width abstract in the native prelude. Until a pinned
    /// `USize.ofNat` exists, no portable arithmetic definition/instance may be
    /// advertised under the fixed-width lane.
    #[test]
    fn test_usize_arithmetic_is_honestly_unwired() {
        let env = Environment::with_prelude();
        for op in ["add", "sub", "mul"] {
            assert!(
                env.get_const(&Name::from_string(&format!("USize.{op}")))
                    .is_none(),
                "USize.{op} must stay absent until platform width is bound"
            );
        }
        for class in ["HAdd", "HSub", "HMul"] {
            assert!(
                !env.is_instance(&Name::from_string(&format!("inst{class}USize"))),
                "inst{class}USize must not claim portable fixed-width semantics"
            );
        }
    }
}

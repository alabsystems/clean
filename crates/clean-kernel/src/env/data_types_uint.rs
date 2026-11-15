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

/// The concrete fixed-width UInt carriers the prelude overlay defines
/// arithmetic and conversions over (`USize` is deliberately absent — see
/// [`Environment::uint_conversion_decl`]).
pub(crate) const FIXED_WIDTH_UINTS: [&str; 4] = ["UInt8", "UInt16", "UInt32", "UInt64"];

/// `("UInt16", "UInt8")` → `"UInt16.toUInt8"`: the Lean 4 name of a width
/// conversion.
pub(crate) fn uint_conversion_name(source: &str, target: &str) -> String {
    format!("{source}.to{target}")
}

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
    /// `.sub`, `.mul`, `.div`, `.mod`, `.land`, `.lor` over the BitVec-backed
    /// carrier, defined THROUGH the
    /// existing `.toNat` (carrier → Nat) and `.ofNat` (Nat → carrier, which
    /// wraps mod 2^w via `Fin.ofNat`), so no new arithmetic axioms are
    /// introduced and every op is kernel-checked at registration:
    ///
    /// ```text
    /// <Name>.add  a b := <Name>.ofNat (Nat.add a.toNat b.toNat)   -- wraps
    /// <Name>.sub  a b := <Name>.ofNat (Nat.add a.toNat (Nat.sub <Name>.size b.toNat))
    /// <Name>.mul  a b := <Name>.ofNat (Nat.mul a.toNat b.toNat)   -- wraps
    /// <Name>.div  a b := <Name>.ofNat (Nat.div  a.toNat b.toNat)  -- never wraps
    /// <Name>.mod  a b := <Name>.ofNat (Nat.mod  a.toNat b.toNat)  -- never wraps
    /// <Name>.land a b := <Name>.ofNat (Nat.land a.toNat b.toNat)  -- never wraps
    /// <Name>.lor  a b := <Name>.ofNat (Nat.lor  a.toNat b.toNat)  -- never wraps
    /// ```
    ///
    /// `sub` uses the two's-complement identity `a - b ≡ a + (2^w - b)` so it
    /// stays inside `Nat` (no `Nat.sub` truncation surprise on the result),
    /// then `.ofNat` reduces mod `<Name>.size = 2^w`. This is the machine
    /// (wrapping) semantics the design's §1.1 domain-tagged arithmetic
    /// requires for `u32`/`u64` clauses — distinct from `Nat`/`Int`.
    ///
    /// ## Division and modulus are TOTAL, and nothing here can compute two answers
    ///
    /// `Nat.div`/`Nat.mod` are total, and Clean's OWN definitions say so — this
    /// is read off `init_nat`, not assumed from Lean. `Nat.div`'s value is
    /// `Nat.rec _ Nat.zero (fun nPred _ => Nat.divCore a a (succ nPred)) n`,
    /// whose `n = 0` branch is literally `Nat.zero`; and `Nat.mod a n =
    /// Nat.modCore a a n`, whose `n <= a` test (`n - a = 0`) is vacuously true
    /// at `n = 0`, so it recurses on `a - 0 = a` until the fuel runs out and
    /// yields `a`. That is exactly Lean 4's `Nat.div_zero` / `Nat.mod_zero`:
    /// `n / 0 = 0`, `n % 0 = n`.
    ///
    /// A ground `<Name>.div x y` reduces as: delta on `<Name>.div` →
    /// `<Name>.ofNat (Nat.div (<Name>.toNat x) (<Name>.toNat y))` → the `toNat`s
    /// reach `Nat` literals → `Nat.div`'s NATIVE reducer fires (`checked_div_big`,
    /// "div by zero => 0"). The `Nat`-level definition and the `Nat`-level
    /// reducer already agree at the zero divisor, and that agreement predates
    /// this overlay — no new decision is being taken here.
    ///
    /// The PER-WIDTH reducers `UInt{N}.div/.mod/.land/.lor`
    /// (`native_reducers_uint.rs`) have been keyed on these names since before
    /// any constant carried them. They do not in fact fire on well-typed terms:
    /// `reduce_native` (`tc/def_eq/delta_helpers.rs`) pre-WHNFs operands only for
    /// `decide` and the wrapper COMPARISON reducers, so an arithmetic reducer
    /// sees `<Name>.ofNat 7` rather than a bare `Nat` literal and declines. They
    /// were checked against these bodies anyway, because a name-keyed reducer
    /// that DID fire and disagreed would give one ground term two values:
    /// `reduce_uint_div` is `checked_div(b).unwrap_or(0)` and `reduce_uint_mod`
    /// returns `a` at `b == 0` — the same answers as the `Nat` bodies, at the
    /// zero divisor and everywhere else.
    ///
    /// The results are all `<= max(a.toNat, b.toNat) < <Name>.size`, so the
    /// `.ofNat` wrap is the identity on them — machine `/`, `%`, `&&&` and
    /// `|||` never overflow.
    ///
    /// `land`/`lor` are declared here even though `Nat.land`/`Nat.lor` are still
    /// bare AXIOMS at this point in the prelude (`data_types_nat.rs`); the full
    /// prelude DISCHARGES them to real `Nat.bitwise` definitions later
    /// (`register_nat_bitwise_def`), and `Environment::axiom_deps` is computed
    /// live against the environment as it stands, so `<Name>.land` is axiom-free
    /// under `with_prelude()`. This is the same ordering `instHAndNat`
    /// (registered even earlier) already relies on.
    ///
    /// ## `xor`, `shiftLeft`, `shiftRight` — transcribed from Lean v4.30.0-rc2
    ///
    /// `src/Init/Data/UInt/Basic.lean` (identical at every width, `<w>` the bit
    /// width):
    ///
    /// ```text
    /// protected def UInt8.xor        (a b : UInt8) : UInt8 := ⟨a.toBitVec ^^^ b.toBitVec⟩
    /// protected def UInt8.shiftLeft  (a b : UInt8) : UInt8 := ⟨a.toBitVec <<< (UInt8.mod b 8).toBitVec⟩
    /// protected def UInt8.shiftRight (a b : UInt8) : UInt8 := ⟨a.toBitVec >>> (UInt8.mod b 8).toBitVec⟩
    /// ```
    ///
    /// with, from `src/Init/Data/BitVec/Basic.lean`, `BitVec.xor x y =
    /// (x.toNat ^^^ y.toNat)#'_`, `BitVec.shiftLeft x s = BitVec.ofNat n
    /// (x.toNat <<< s)`, `BitVec.ushiftRight x s = (x.toNat >>> s)#'_`, `x <<< (y
    /// : BitVec _) = x <<< y.toNat`, and `BitVec.umod x y = (x.toNat % y.toNat)#'_`.
    /// Read through `.toNat`, in this overlay's existing `ofNat ∘ Nat.op ∘ toNat`
    /// idiom, that is:
    ///
    /// ```text
    /// <Name>.xor        a b := <Name>.ofNat (Nat.xor a.toNat b.toNat)
    /// <Name>.shiftLeft  a b := <Name>.ofNat (Nat.shiftLeft a.toNat (Nat.mod b.toNat <w>))
    /// <Name>.shiftRight a b := <Name>.ofNat (Nat.div a.toNat (Nat.pow 2 (Nat.mod b.toNat <w>)))
    /// ```
    ///
    /// **The shift amount is reduced MODULO THE WIDTH** — `(1 : UInt8) <<< 8 = 1`
    /// and `(1 : UInt64) <<< 65 = 2`, neither `0` nor a trap. That is Lean's
    /// semantics, not Rust's (`<<` by `>= width` panics or is masked per build
    /// profile), and it is the one place a plausible-looking body would be
    /// wrong. `shiftLeft` then wraps mod `2^w` through `.ofNat` (it is the only
    /// one of the three that can overflow); `xor` and `shiftRight` results are
    /// `<= max(a.toNat, b.toNat)`, so their `.ofNat` is the identity.
    ///
    /// `shiftRight` is stated through `Nat.div`/`Nat.pow` rather than
    /// `Nat.shiftRight`, and that is deliberate. `Nat.shiftRight` is still a bare
    /// AXIOM on the `with_prelude` path (`data_types_nat.rs`: "Only
    /// `Nat.shiftRight` stays an axiom"; its discharge,
    /// `register_nat_shiftright_def`, runs only for the soundness certificate and
    /// the clean-verify spec build), so a body through it would make
    /// `<Name>.shiftRight` the one axiom-BEARING constant in this overlay. Lean
    /// core proves `Nat.shiftRight_eq_div_pow : m >>> n = m / 2 ^ n`
    /// (`src/Init/Data/Nat/Bitwise/Basic.lean`), so the two bodies denote the
    /// same function; this one is built from two real definitions and is
    /// axiom-free under every construction path.
    ///
    /// The per-width native reducers keyed on these three names
    /// (`reduce_small_shift_left` & co.) already reduce the amount mod the width
    /// and are pinned against these bodies at the edges (amount `0`, `w - 1`,
    /// `w`, `w + 1`, the maximum value) by
    /// `test_uint_xor_shift_bodies_agree_with_native_reducers`.
    ///
    /// The caller (`init_uint_arith`) requires a concrete-width `<Name>` already
    /// initialized (its `.toNat`/`.ofNat`/`.size`) plus `init_nat`. `USize` is
    /// deliberately excluded: its width is platform-abstract and the native
    /// prelude has no canonical `USize.ofNat` to ground these definitions.
    fn init_one_uint_arith(&mut self, name: &str) -> Result<(), EnvError> {
        // Fail closed on anything but the four concrete widths: the shift
        // bodies below bake the width in as a literal, and a guessed width
        // would be a silently wrong machine operation.
        let width = Self::fixed_uint_width(name)
            .ok_or_else(|| EnvError::UnknownInductive(Name::from_string(name)))?;
        let ty = Expr::const_(Name::from_string(name), vec![]);
        let to_nat = Expr::const_(Name::from_string(&format!("{name}.toNat")), vec![]);
        let of_nat = Expr::const_(Name::from_string(&format!("{name}.ofNat")), vec![]);
        let size = Expr::const_(Name::from_string(&format!("{name}.size")), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_div = Expr::const_(Name::from_string("Nat.div"), vec![]);
        let nat_mod = Expr::const_(Name::from_string("Nat.mod"), vec![]);
        let nat_land = Expr::const_(Name::from_string("Nat.land"), vec![]);
        let nat_lor = Expr::const_(Name::from_string("Nat.lor"), vec![]);

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
        let div_val = mk_binop(&|x, y| Expr::apps(nat_div.clone(), [x, y]));
        let mod_val = mk_binop(&|x, y| Expr::apps(nat_mod.clone(), [x, y]));
        let land_val = mk_binop(&|x, y| Expr::apps(nat_land.clone(), [x, y]));
        let lor_val = mk_binop(&|x, y| Expr::apps(nat_lor.clone(), [x, y]));
        let nat_xor = Expr::const_(Name::from_string("Nat.xor"), vec![]);
        let nat_shl = Expr::const_(Name::from_string("Nat.shiftLeft"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let xor_val = mk_binop(&|x, y| Expr::apps(nat_xor.clone(), [x, y]));
        // The shift AMOUNT, reduced mod the width — Lean's `(<Name>.mod b <w>)`.
        let nat_mod_c = nat_mod.clone();
        let amount = move |y: Expr| Expr::apps(nat_mod_c.clone(), [y, Expr::nat_lit(width)]);
        let amount_l = amount.clone();
        let shl_val = mk_binop(&|x, y| Expr::apps(nat_shl.clone(), [x, amount_l(y)]));
        let nat_div_c = nat_div.clone();
        let shr_val = mk_binop(&|x, y| {
            // x / 2^(y % w)  ==  x >>> (y % w)   (`Nat.shiftRight_eq_div_pow`)
            let pow = Expr::apps(nat_pow.clone(), [Expr::nat_lit(2), amount(y)]);
            Expr::apps(nat_div_c.clone(), [x, pow])
        });

        for (op, value) in [
            ("add", add_val),
            ("sub", sub_val),
            ("mul", mul_val),
            ("div", div_val),
            ("mod", mod_val),
            ("land", land_val),
            ("lor", lor_val),
            ("xor", xor_val),
            ("shiftLeft", shl_val),
            ("shiftRight", shr_val),
        ] {
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

    /// WS6.10: the ONE canonical spelling of the fixed-width conversion
    /// `<source>.toUInt<N>` (`target = "UInt<N>"`), the declaration
    /// [`Self::init_uint_conversions`] registers for every ordered pair of
    /// distinct fixed widths:
    ///
    /// ```text
    /// <source>.to<target> : <source> → <target>
    ///   := fun x => <target>.ofNat (<source>.toNat x)
    /// ```
    ///
    /// This is Lean 4's meaning of the conversion (`UInt16.toUInt8 300 = 44`,
    /// `UInt8.toUInt64 255 = 255`): `<target>.ofNat` wraps mod `2^target`, so
    /// NARROWING truncates and WIDENING is exact because `<source>.toNat x <
    /// 2^source <= 2^target`. Built from the carrier's own `.toNat` / `.ofNat`,
    /// so it adds no axiom and is kernel-checked at registration.
    ///
    /// Why it has to exist: the kernel has named NATIVE REDUCERS for these
    /// twelve names (`native_reducers_uint_conv.rs`) but, before this, no
    /// constant carried them — `def widen (a : UInt8) : UInt64 := a.toUInt64`
    /// failed with "Unknown identifier" (F-107, `GENERAL.p12b_width_conversion`).
    /// With the definition present the reducers are an ACCELERATION of a real
    /// definition, and `native_reducers_uint_conv_tests.rs` checks every one
    /// against this body's δ-unfolding. Because the registration goes through
    /// this same function, the test's "canonical body" and the registered
    /// constant cannot drift apart into two spellings of one name.
    ///
    /// The eight `USize` conversions stay OUT, for the reason every other
    /// constant of this overlay excludes `USize`: its width is platform-
    /// abstract and the native prelude has no canonical `USize.ofNat`.
    pub(crate) fn uint_conversion_decl(source: &str, target: &str) -> Declaration {
        let src_ty = Expr::const_(Name::from_string(source), vec![]);
        let dst_ty = Expr::const_(Name::from_string(target), vec![]);
        let src_to_nat = Expr::const_(Name::from_string(&format!("{source}.toNat")), vec![]);
        let dst_of_nat = Expr::const_(Name::from_string(&format!("{target}.ofNat")), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(src_ty.clone());
            let body = Expr::app(dst_of_nat, Expr::app(src_to_nat, x));
            let e = b.mk_lam(x_id, BinderInfo::Default, src_ty.clone(), body);
            b.finish(e)
        };
        Declaration::Definition {
            name: Name::from_string(&uint_conversion_name(source, target)),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, src_ty, dst_ty),
            value,
            is_reducible: true,
        }
    }

    /// Trust: wrapping machine arithmetic + `HAdd`/`HSub`/`HMul`/`HDiv`/`HMod`/
    /// `HAnd`/`HOr` instances for
    /// every concrete fixed-width UInt (`UInt8/16/32/64`, two-language design
    /// §1.1). After this,
    /// `x + 1 : UInt64` and friends elaborate against the single-file prelude,
    /// so the spec elaborator can target machine-typed goals. `USize` remains
    /// intentionally unavailable until a platform-width-bound `USize.ofNat`
    /// exists; claiming portable wrap semantics without that binding would be
    /// unsound. Idempotent and retry-safe after any partially completed call.
    ///
    /// MEASURED GAP THIS CLOSES (2026-08-22): before `HDiv`/`HMod`/`HAnd`/`HOr`
    /// joined the table, `def v (a b : UInt64) : UInt64 := a % b` did not
    /// elaborate at ANY UInt width — not even between two variables — while the
    /// same body at `Nat` did. The `H*` CLASSES already existed and the native
    /// reducers for `UInt{N}.div/.mod/.land/.lor` were already registered; only
    /// the backing constants and the instances were missing.
    ///
    /// MEASURED GAP THIS CLOSES (2026-09-16): `a ^^^ b`, `a <<< b`, `a >>> b`
    /// and `a.toUInt64` did not elaborate at any UInt width (`failed to
    /// synthesize instance HXor UInt64 UInt64 UInt64`; `Unknown projection field
    /// toUInt64 on structure UInt8`), so a hash, a checksum, a bit-pack or any
    /// mixed-width helper could not even be STATED against this prelude — in a
    /// definition or in a theorem.
    ///
    /// This comment used to say `^^^`/`<<<`/`>>>` were deliberately left out,
    /// for two reasons. Both were re-examined rather than inherited:
    ///
    /// * *"`Nat.shiftRight` is an admitted axiom on the `with_prelude` path, so
    ///   `UInt{N}.shiftRight` would be axiom-bearing."* Still true of
    ///   `Nat.shiftRight`, and the reason `UInt{N}.shiftRight` is NOT built on
    ///   it — see `init_one_uint_arith`. The overlay stays axiom-free
    ///   (`test_uint8_defs_axiom_free_and_arith_overlay_axiom_free`).
    /// * *"The shift classes are `homogeneous: false` in the elaborator, so it
    ///   is a different elaboration problem."* Half right, and the half that
    ///   was right needed a second fix rather than a refusal. `homogeneous:
    ///   false` is correct — Lean does not route `<<<`/`>>>` through `binop%`
    ///   either (`src/Init/Notation.lean` gives only `^^^` a `binop%` rule) —
    ///   and the MEASURED failure (`a <<< b`, two variables) had all three slots
    ///   already resolved to `UInt64`, so for it the missing instance was the
    ///   whole story. A NUMERAL amount (`a <<< 3`, `(1 : UInt64) <<< 65`) was
    ///   not: it defaulted to `Nat` and asked for `HShiftLeft UInt64 Nat
    ///   UInt64`, which exists in neither prelude. Lean types it at the carrier
    ///   because `@[default_instance] instance [ShiftLeft α] : HShiftLeft α α α`
    ///   outranks `@[default_instance 100] instOfNatNat`; Clean now does the
    ///   same by resolving the actual dictionary in the numeral pass
    ///   (`ElabCtx::resolve_shift_numeral_instance`), so the homogeneous
    ///   premise is checked and a typed Nat operand keeps its own type.
    ///
    /// Instances are registered directly at `H{Xor,ShiftLeft,ShiftRight} W W W`,
    /// the shape Lean reaches through its `@[default_instance]` bridges
    /// (`instance [ShiftLeft α] : HShiftLeft α α α`, `src/Init/Prelude.lean`) and
    /// the shape every other row of this table already uses.
    ///
    /// The conversions are the F-107 half of that gap (WS6.10,
    /// `GENERAL.p12b_width_conversion`): the twelve fixed-width
    /// `UInt{8,16,32,64}.toUInt{8,16,32,64}` had named native reducers and NO
    /// constant, so `a.toUInt64` was "Unknown identifier". Each is now a real
    /// definition, registered by `init_uint_conversions` from the one canonical
    /// spelling [`Self::uint_conversion_decl`]. In IMPORT MODE the guard below
    /// skips them with the rest of the overlay: the genuine Lean declarations
    /// enter through checked import instead.
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
        self.init_hdiv()?;
        self.init_hmod()?;
        self.init_hand()?;
        self.init_hor()?;
        self.init_hxor()?;
        self.init_hshiftleft()?;
        self.init_hshiftright()?;
        // Arithmetic literals (`x + 1`) require the OfNat resolver entry for
        // the actual carrier width, not merely the UInt64 instance.
        self.init_ofnat_uint8()?;
        self.init_ofnat_uint16()?;
        self.init_ofnat_uint32()?;
        self.init_ofnat_uint64()?;

        for name in FIXED_WIDTH_UINTS {
            self.init_one_uint_arith(name)?;
            for (class, op) in [("ShiftLeft", "shiftLeft"), ("ShiftRight", "shiftRight")] {
                self.add_homogeneous_shift_instance(class, name, &format!("{name}.{op}"))?;
            }
            for (class, ctor, op) in [
                ("HAdd", "HAdd.mk", "add"),
                ("HSub", "HSub.mk", "sub"),
                ("HMul", "HMul.mk", "mul"),
                ("HDiv", "HDiv.mk", "div"),
                ("HMod", "HMod.mk", "mod"),
                ("HAnd", "HAnd.mk", "land"),
                ("HOr", "HOr.mk", "lor"),
                ("HXor", "HXor.mk", "xor"),
                ("HShiftLeft", "HShiftLeft.mk", "shiftLeft"),
                ("HShiftRight", "HShiftRight.mk", "shiftRight"),
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
        self.init_uint_conversions()?;
        Ok(())
    }

    /// Bit width of a concrete fixed-width UInt carrier, `None` for anything
    /// else — `USize` included, on purpose: its width is
    /// `System.Platform.numBits`, opaque in the kernel exactly as in Lean, so no
    /// literal stands for it.
    fn fixed_uint_width(name: &str) -> Option<u64> {
        match name {
            "UInt8" => Some(8),
            "UInt16" => Some(16),
            "UInt32" => Some(32),
            "UInt64" => Some(64),
            _ => None,
        }
    }

    /// Trust: the twelve fixed-width conversions `UInt{N}.toUInt{M}` (`N != M`)
    /// and the four `Nat.toUInt{N}` abbreviations — the everyday `as u64` /
    /// `as u8`. Transcribed from Lean v4.30.0-rc2
    /// `src/Init/Data/UInt/BasicAux.lean`:
    ///
    /// ```text
    /// abbrev Nat.toUInt8 := UInt8.ofNat
    /// def UInt64.toUInt8 (a : UInt64) : UInt8  := a.toNat.toUInt8          -- narrowing
    /// def UInt8.toUInt64 (a : UInt8)  : UInt64 :=
    ///   ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩              -- widening
    /// ```
    ///
    /// Both directions are declared here as ONE body,
    ///
    /// ```text
    /// UInt{N}.toUInt{M} a := UInt{M}.ofNat (UInt{N}.toNat a)
    /// ```
    ///
    /// For NARROWING that is Lean's body verbatim once the `Nat.toUInt{M}`
    /// abbreviation is unfolded: truncation, `a.toNat % 2^M`. For WIDENING
    /// Lean's body carries `a.toNat` with a bound proof instead of reducing it;
    /// the two agree on every value because `a.toNat < 2^N <= 2^M` makes
    /// `a.toNat % 2^M = a.toNat` — zero-extension, and the `%` never bites. The
    /// proof-carrying spelling is not used because it would need `BitVec.isLt`
    /// and a `decide` on `2^N < 2^M` assembled by hand for no change in value;
    /// the deviation is definitional shape only, the same one every arithmetic
    /// row of this overlay already has against Lean's `⟨a.toBitVec + …⟩`.
    ///
    /// The native reducers keyed on these names (`native_reducers_uint_conv.rs`:
    /// `n % 2^M` narrowing, identity widening) compute the same function and
    /// are pinned against these bodies by
    /// `test_uint_conversion_bodies_agree_with_native_reducers` and, over every
    /// width pair at both widths' boundary values plus a wrong-width mutation
    /// control, by `native_reducers_uint_conv_tests.rs` (WS6.10). Like the
    /// arithmetic reducers they accept only a bare `Nat` literal operand, so
    /// they decline on a well-typed `UInt{N}` term and the body is what reduces.
    ///
    /// The twelve `UInt{N}.toUInt{M}` bodies are built by ONE function,
    /// [`Self::uint_conversion_decl`], so the constant the prelude registers
    /// and the canonical shape the tests compare against are the same
    /// spelling by construction (this landed twice on divergent lines — the
    /// `^^^`/`<<<`/`>>>` batch and WS6.10 — with byte-identical bodies; the
    /// merge kept one builder rather than two agreeing copies).
    ///
    /// `USize` conversions stay absent: the target (or source) width is opaque.
    fn init_uint_conversions(&mut self) -> Result<(), EnvError> {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        for to in FIXED_WIDTH_UINTS {
            let to_ty = Expr::const_(Name::from_string(to), vec![]);
            let of_nat = Expr::const_(Name::from_string(&format!("{to}.ofNat")), vec![]);
            // abbrev Nat.toUInt{M} := UInt{M}.ofNat, at Lean's type
            // `(n : @& Nat) → UInt{M}`: the borrowed-argument annotation is
            // `mdata {borrowed := true}` on the binder domain in the stored
            // type (pinned v4.30.0-rc2, `repr` of `Nat.toUInt8`'s type), and
            // the collision census compares the stored type.
            self.ensure_exact_checked_decl(Declaration::Definition {
                name: Name::from_string(&format!("Nat.to{to}")),
                level_params: vec![],
                type_: Expr::pi(
                    BinderInfo::Default,
                    crate::env::lean_nat_spelling::LeanNat::borrowed(nat.clone()),
                    to_ty.clone(),
                ),
                value: of_nat.clone(),
                is_reducible: true,
            })?;
            for from in FIXED_WIDTH_UINTS {
                if from == to {
                    continue;
                }
                self.ensure_exact_checked_decl(Self::uint_conversion_decl(from, to))?;
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

    /// Census every shift dictionary, including quantified bridges. The four
    /// BitVec dictionaries have exact Nat or independently sized BitVec inputs;
    /// every other prelude dictionary remains homogeneous. No entry is skipped.
    #[test]
    fn test_prelude_shift_instance_carriers_are_exact() {
        let env = Environment::with_prelude();
        let mut checked = 0usize;
        let mut bitvec_checked = 0usize;
        for class in ["HShiftLeft", "HShiftRight"] {
            let class_name = Name::from_string(class);
            for inst in env.get_class_instances(&class_name) {
                let info = env.get_const(&inst.name).unwrap_or_else(|| {
                    panic!(
                        "instance {} is registered for {class} but has no declaration",
                        inst.name
                    )
                });
                let mut ty = &info.type_;
                let mut parameters = Vec::new();
                while let ExprKind::Pi(binder, parameter, body) = ty.kind() {
                    parameters.push((binder.info, parameter.clone()));
                    ty = body;
                }
                assert!(
                    is_const(ty.get_app_fn(), class),
                    "instance {} must be a {class} application, got head {:?}",
                    inst.name,
                    ty.get_app_fn().kind(),
                );
                let args = ty.get_app_args();
                assert_eq!(
                    args.len(),
                    3,
                    "instance {} : {class} must take exactly 3 type arguments, got {}",
                    inst.name,
                    args.len(),
                );
                let bitvec_nat_name = format!("BitVec.inst{class}Nat");
                let bitvec_name = format!("BitVec.inst{class}");
                let name = inst.name.to_string();
                if name == bitvec_nat_name || name == bitvec_name {
                    assert_eq!(args[0], args[2], "BitVec result preserves its width");
                    assert!(is_const(args[0].get_app_fn(), "BitVec"));
                    let bitvec_amount = name == bitvec_name;
                    assert_eq!(parameters.len(), if bitvec_amount { 2 } else { 1 });
                    for (binder, parameter) in &parameters {
                        assert_eq!(*binder, BinderInfo::Implicit);
                        assert_eq!(
                            parameter.as_ref(),
                            &Expr::const_(Name::from_string("Nat"), vec![])
                        );
                    }
                    assert_eq!(
                        args[0].get_app_args().as_slice(),
                        &[&Expr::bvar(if bitvec_amount { 1 } else { 0 })]
                    );
                    if bitvec_amount {
                        assert!(is_const(args[1].get_app_fn(), "BitVec"));
                        assert_eq!(args[1].get_app_args().as_slice(), &[&Expr::bvar(0)]);
                    } else {
                        assert_eq!(args[1], &Expr::const_(Name::from_string("Nat"), vec![]));
                    }
                    bitvec_checked += 1;
                } else {
                    assert!(
                        args[0] == args[1] && args[1] == args[2],
                        "HETEROGENEOUS prelude shift instance {} : {class} {:?} {:?} {:?}; \
                     keep the full heterogeneous amount semantics explicit.",
                        inst.name,
                        args[0].kind(),
                        args[1].kind(),
                        args[2].kind(),
                    );
                }
                checked += 1;
            }
        }
        assert_eq!(bitvec_checked, 4, "both amount types at both shift classes");
        // Non-vacuity: the invariant is only worth anything if the prelude
        // actually registers shift instances for it to range over (4 widths x
        // 2 classes at the time of writing).
        assert!(
            checked >= 8 + bitvec_checked,
            "expected at least 8 non-BitVec shift instances plus {bitvec_checked} BitVec instances, \
             saw {checked} -- a vacuous pass means the lookup, not the prelude, changed",
        );

        // POSITIVE CONTROL for the predicate itself. `instHPowIntNat : HPow
        // Int Nat Int` (`env/algebra_hetero.rs`, via `add_hetero3_instance`) is
        // a genuinely heterogeneous instance this same prelude DOES register,
        // so the `args[0] == args[1] == args[2]` test above is measured to
        // discriminate rather than assumed to: if it could not tell the two
        // apart, this assertion would fail and the guard above would be
        // passing vacuously on shape.
        let mut hetero_seen = 0usize;
        for inst in env.get_class_instances(&Name::from_string("HPow")) {
            let Some(info) = env.get_const(&inst.name) else {
                continue;
            };
            let args = info.type_.get_app_args();
            if args.len() == 3 && !(args[0] == args[1] && args[1] == args[2]) {
                hetero_seen += 1;
            }
        }
        assert!(
            hetero_seen >= 1,
            "positive control: expected at least one HETEROGENEOUS HPow instance \
             (instHPowIntNat : HPow Int Nat Int) so the homogeneity test above is \
             measured to have teeth; saw {hetero_seen}",
        );
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

    /// `UInt8.toNat`/`ofNat`/`toBitVec` are axiom-free reducible defs, and the
    /// whole fixed-width arithmetic overlay is axiom-free too.
    ///
    /// RESTATED 2026-08-22. This test used to assert `{w}.mod` was ABSENT. The
    /// property it was defending is named in its own history — *"an opaque
    /// modulus would add proof authority"*, i.e. the historical `UInt8.mod`
    /// AXIOM must not come back. Absence was a proxy for that, and it was the
    /// wrong proxy: it also forbade the axiom-FREE `Declaration::Definition`
    /// built from `Nat.mod`, which is the thing that makes `a % b` elaborate at
    /// a machine width at all. Assert the real property — every constant in the
    /// overlay is a Definition with an EMPTY axiom closure — so a reintroduced
    /// axiom still fails, and `USize` stays out entirely.
    #[test]
    fn test_uint8_defs_axiom_free_and_arith_overlay_axiom_free() {
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
        for w in ["UInt8", "UInt16", "UInt32", "UInt64"] {
            for op in [
                "add",
                "sub",
                "mul",
                "div",
                "mod",
                "land",
                "lor",
                "xor",
                "shiftLeft",
                "shiftRight",
            ]
            .into_iter()
            .map(String::from)
            .chain(
                // The cross-width conversions are part of the same overlay and
                // carry the same obligation.
                ["UInt8", "UInt16", "UInt32", "UInt64"]
                    .into_iter()
                    .filter(|to| *to != w)
                    .map(|to| format!("to{to}")),
            ) {
                let cname = format!("{w}.{op}");
                let name = Name::from_string(&cname);
                let info = env
                    .get_const(&name)
                    .unwrap_or_else(|| panic!("{cname} must be registered"));
                assert_eq!(
                    info.kind,
                    crate::env::types::ConstantKind::Definition,
                    "{cname} must be a Definition, never an Axiom — an opaque \
                     machine operation would add proof authority"
                );
                let deps = env.axiom_deps(&name).expect("registered above");
                let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
                assert!(
                    names.is_empty(),
                    "{cname} must be axiom-free, got {names:?}"
                );
            }
        }
        // USize is width-abstract: NO arithmetic constant may exist for it.
        for op in [
            "add",
            "sub",
            "mul",
            "div",
            "mod",
            "land",
            "lor",
            "xor",
            "shiftLeft",
            "shiftRight",
        ] {
            assert!(
                env.get_const(&Name::from_string(&format!("USize.{op}")))
                    .is_none(),
                "USize.{op} must stay absent until platform width is bound"
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

    /// The `/ % &&& |||` bodies compute, and — the load-bearing half — the
    /// ZERO DIVISOR reduces to the same value the pre-registered native
    /// reducers (`reduce_uint_div`, `reduce_uint_mod`) produce for these very
    /// names. Had the two disagreed, declaring the constant would have given
    /// one ground term two values.
    #[test]
    fn test_uint8_div_mod_bitwise_values_and_zero_divisor() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for (actual, expected, label) in [
            (uint8_binop("div", 7, 2), uint8(3), "7 / 2 = 3"),
            (uint8_binop("mod", 7, 3), uint8(1), "7 % 3 = 1"),
            (uint8_binop("div", 255, 16), uint8(15), "255 / 16 = 15"),
            (uint8_binop("mod", 255, 16), uint8(15), "255 % 16 = 15"),
            (
                uint8_binop("land", 0xF0, 0x3C),
                uint8(0x30),
                "0xF0 &&& 0x3C",
            ),
            (uint8_binop("lor", 0xF0, 0x0C), uint8(0xFC), "0xF0 ||| 0x0C"),
            // Lean 4 total semantics: `n / 0 = 0`, `n % 0 = n`.
            (uint8_binop("div", 7, 0), uint8(0), "7 / 0 = 0"),
            (uint8_binop("mod", 7, 0), uint8(7), "7 % 0 = 7"),
            (uint8_binop("div", 0, 0), uint8(0), "0 / 0 = 0"),
            (uint8_binop("mod", 0, 0), uint8(0), "0 % 0 = 0"),
        ] {
            assert!(
                tc.is_def_eq(&actual, &expected),
                "UInt8 {label} must reduce to the stated value"
            );
        }
    }

    /// The same zero-divisor semantics at the widest carrier, where the native
    /// reducer is a different function (`reduce_u64_*` rather than the
    /// modulus-taking `reduce_small_*`).
    #[test]
    fn test_uint64_div_mod_zero_divisor() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let u64_of = |n: u64| {
            Expr::app(
                Expr::const_(Name::from_string("UInt64.ofNat"), vec![]),
                Expr::nat_lit(n),
            )
        };
        let binop = |op: &str, a: u64, b: u64| {
            Expr::apps(
                Expr::const_(Name::from_string(&format!("UInt64.{op}")), vec![]),
                [u64_of(a), u64_of(b)],
            )
        };
        for (actual, expected, label) in [
            (binop("div", 7, 2), u64_of(3), "7 / 2 = 3"),
            (binop("mod", 7, 3), u64_of(1), "7 % 3 = 1"),
            (binop("div", 7, 0), u64_of(0), "7 / 0 = 0"),
            (binop("mod", 7, 0), u64_of(7), "7 % 0 = 7"),
        ] {
            assert!(
                tc.is_def_eq(&actual, &expected),
                "UInt64 {label} must reduce to the stated value"
            );
        }
    }

    // ── xor / shiftLeft / shiftRight / toUInt{M} ───────────────────────────

    /// `(carrier, bit width)`.
    const BIT_WIDTHS: [(&str, u32); 4] =
        [("UInt8", 8), ("UInt16", 16), ("UInt32", 32), ("UInt64", 64)];

    fn uint_of(carrier: &str, n: u64) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string(&format!("{carrier}.ofNat")), vec![]),
            Expr::nat_lit(n),
        )
    }

    fn uint_binop(carrier: &str, op: &str, a: u64, b: u64) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string(&format!("{carrier}.{op}")), vec![]),
            [uint_of(carrier, a), uint_of(carrier, b)],
        )
    }

    fn uint_to_nat(carrier: &str, e: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string(&format!("{carrier}.toNat")), vec![]),
            e,
        )
    }

    fn max_of(bits: u32) -> u64 {
        if bits == 64 {
            u64::MAX
        } else {
            (1u64 << bits) - 1
        }
    }

    /// Lean 4's semantics, written independently of BOTH things under test (the
    /// declared bodies and the native reducers), in `u128` so nothing here can
    /// wrap by accident: shift amount mod the width, result mod `2^width`.
    fn lean_model(op: &str, bits: u32, a: u64, b: u64) -> u64 {
        let modulus = 1u128 << bits;
        let amount = u128::from(b) % u128::from(bits);
        let r = match op {
            "xor" => u128::from(a ^ b),
            "shiftLeft" => (u128::from(a) << amount) % modulus,
            "shiftRight" => u128::from(a) >> amount,
            other => panic!("no model for {other}"),
        };
        u64::try_from(r).expect("result fits the carrier")
    }

    /// Facts that are TRUE in Lean 4 (each is `by decide` / `rfl` there), and
    /// for each one a CLOSE NEGATIVE TWIN the kernel must refuse. The twins are
    /// not arbitrary wrong numbers: each is the answer a plausible WRONG
    /// semantics would give — shift-by-width-is-zero (`checked_shl`), Rust's
    /// unmasked shift, a non-wrapping left shift, `or` in place of `xor`.
    #[test]
    fn test_uint_xor_shift_values_match_lean_and_reject_near_misses() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        // (carrier, op, a, b, Lean's answer, the near-miss that must be refused)
        let cases: &[(&str, &str, u64, u64, u64, u64)] = &[
            // xor — `0xF0F0 ^^^ 0xFF00 = 0x0FF0` is probe 07d; twin is `|||`.
            ("UInt64", "xor", 0xF0F0, 0xFF00, 0x0FF0, 0xFFF0),
            ("UInt8", "xor", 0xFF, 0xFF, 0, 0xFF),
            ("UInt8", "xor", 0xAA, 0x55, 0xFF, 0),
            ("UInt64", "xor", u64::MAX, 1, u64::MAX - 1, u64::MAX),
            // shiftLeft — amount is taken MOD THE WIDTH. `1 <<< 65 = 2` is probe
            // 07e; the twin `0` is what `checked_shl(..).unwrap_or(0)` answers.
            ("UInt64", "shiftLeft", 1, 3, 8, 4),
            ("UInt64", "shiftLeft", 1, 65, 2, 0),
            ("UInt64", "shiftLeft", 1, 64, 1, 0),
            ("UInt8", "shiftLeft", 1, 8, 1, 0),
            ("UInt8", "shiftLeft", 1, 254, 64, 0),
            // ... and the RESULT wraps mod 2^w; the twin is the unwrapped value.
            ("UInt8", "shiftLeft", 0xFF, 1, 0xFE, 0x1FE),
            ("UInt8", "shiftLeft", 0x81, 1, 0x02, 0x102),
            ("UInt64", "shiftLeft", u64::MAX, 63, 1 << 63, u64::MAX),
            ("UInt16", "shiftLeft", 1, 17, 2, 0),
            ("UInt32", "shiftLeft", 1, 33, 2, 0),
            // shiftRight — same amount rule; logical (zero-filling).
            ("UInt64", "shiftRight", 0xF0, 4, 0x0F, 0xF0),
            ("UInt64", "shiftRight", 8, 67, 1, 0),
            ("UInt64", "shiftRight", u64::MAX, 64, u64::MAX, 0),
            ("UInt64", "shiftRight", u64::MAX, 63, 1, u64::MAX),
            ("UInt8", "shiftRight", 0x80, 7, 1, 0xFF),
            ("UInt8", "shiftRight", 0x80, 8, 0x80, 0),
            ("UInt8", "shiftRight", 0x80, 9, 0x40, 0),
            ("UInt16", "shiftRight", 0x8000, 16, 0x8000, 0),
            ("UInt32", "shiftRight", 0x8000_0000, 32, 0x8000_0000, 0),
        ];
        for &(carrier, op, a, b, expected, near_miss) in cases {
            let bits = BIT_WIDTHS
                .iter()
                .find(|(c, _)| *c == carrier)
                .expect("known carrier")
                .1;
            assert_eq!(
                lean_model(op, bits, a, b),
                expected,
                "test table is wrong about Lean: {carrier}.{op} {a} {b}"
            );
            assert_ne!(
                expected, near_miss,
                "a twin equal to the answer tests nothing"
            );
            let term = uint_binop(carrier, op, a, b);
            assert!(
                tc.is_def_eq(&term, &uint_of(carrier, expected)),
                "{carrier}.{op} {a:#x} {b} must reduce to {expected:#x}"
            );
            // The twin is compared at `Nat`, through `.toNat`, NOT by wrapping it
            // into the carrier: `UInt8.ofNat 0x1FE` IS `0xFE`, so a carrier-level
            // comparison would silently turn the "did not wrap" twin into the
            // right answer and the refusal below into a false alarm.
            let as_nat = uint_to_nat(carrier, term);
            assert!(tc.is_def_eq(&as_nat, &Expr::nat_lit(expected)));
            assert!(
                !tc.is_def_eq(&as_nat, &Expr::nat_lit(near_miss)),
                "({carrier}.{op} {a:#x} {b}).toNat = {near_miss:#x} is FALSE in Lean \
                 and must be refused"
            );
        }
    }

    /// The per-width native reducers have been keyed on `UInt{N}.xor`,
    /// `.shiftLeft` and `.shiftRight` since before any constant carried those
    /// names. Declaring the constants is what makes a disagreement possible, so
    /// the three are pinned against each other at every width and every edge:
    /// the DECLARED BODY (kernel reduction), the NATIVE REDUCER (called
    /// directly, on the bare literals it accepts), and an independent model of
    /// Lean. A reducer that disagreed with its body would give one ground term
    /// two values.
    #[test]
    fn test_uint_xor_shift_bodies_agree_with_native_reducers() {
        use crate::env::native_reducers_uint as nr;
        type Reducer = fn(&[&Expr]) -> Option<Expr>;
        let reducers: [(&str, [(&str, Reducer); 3]); 4] = [
            (
                "UInt8",
                [
                    ("xor", nr::reduce_uint8_xor),
                    ("shiftLeft", nr::reduce_uint8_shl),
                    ("shiftRight", nr::reduce_uint8_shr),
                ],
            ),
            (
                "UInt16",
                [
                    ("xor", nr::reduce_uint16_xor),
                    ("shiftLeft", nr::reduce_uint16_shl),
                    ("shiftRight", nr::reduce_uint16_shr),
                ],
            ),
            (
                "UInt32",
                [
                    ("xor", nr::reduce_uint32_xor),
                    ("shiftLeft", nr::reduce_uint32_shl),
                    ("shiftRight", nr::reduce_uint32_shr),
                ],
            ),
            (
                "UInt64",
                [
                    ("xor", nr::reduce_uint64_xor),
                    ("shiftLeft", nr::reduce_uint64_shl),
                    ("shiftRight", nr::reduce_uint64_shr),
                ],
            ),
        ];
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for ((carrier, ops), (_, bits)) in reducers.iter().zip(BIT_WIDTHS) {
            let max = max_of(bits);
            let w = u64::from(bits);
            let values = [0, 1, 0x5A, max >> 1, (max >> 1) + 1, max];
            // Amounts: none, one, the last in-range, exactly the width, past it,
            // a multiple of it, and the largest the carrier can express.
            let amounts = [0, 1, w - 1, w, w + 1, 2 * w, max];
            for (op, reducer) in ops {
                for a in values {
                    for b in amounts.into_iter().filter(|b| *b <= max) {
                        let model = lean_model(op, bits, a, b);
                        let (la, lb) = (Expr::nat_lit(a), Expr::nat_lit(b));
                        let native = reducer(&[&la, &lb])
                            .unwrap_or_else(|| panic!("{carrier}.{op} reducer declined"));
                        assert_eq!(
                            native,
                            Expr::nat_lit(model),
                            "NATIVE {carrier}.{op} {a:#x} {b} disagrees with Lean"
                        );
                        let body = uint_to_nat(carrier, uint_binop(carrier, op, a, b));
                        assert!(
                            tc.is_def_eq(&body, &Expr::nat_lit(model)),
                            "BODY {carrier}.{op} {a:#x} {b} must be {model:#x}"
                        );
                        assert!(
                            !tc.is_def_eq(&body, &Expr::nat_lit(model ^ 1)),
                            "BODY {carrier}.{op} {a:#x} {b} must not also be {:#x}",
                            model ^ 1
                        );
                    }
                }
            }
        }
    }

    fn uint_conv(from: &str, to: &str, a: u64) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string(&format!("{from}.to{to}")), vec![]),
            uint_of(from, a),
        )
    }

    /// `toUInt{M}`: widening is zero-extension (the value is unchanged),
    /// narrowing is truncation (`a.toNat % 2^M`). Negative twins: a widening
    /// that sign-extends, a narrowing that saturates or keeps the HIGH byte.
    #[test]
    fn test_uint_conversions_zero_extend_and_truncate() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        // (from, to, a, Lean's answer, near-miss)
        let cases: &[(&str, &str, u64, u64, u64)] = &[
            // probe 06c / 06d
            ("UInt8", "UInt64", 200, 200, u64::MAX - 55), // not sign-extended
            ("UInt64", "UInt8", 0x1234, 0x34, 0x12),      // low byte, not high
            ("UInt64", "UInt8", 0x1234, 0x34, 0xFF),      // truncates, not saturates
            ("UInt8", "UInt16", 0xFF, 0xFF, 0xFFFF),
            ("UInt8", "UInt32", 0x80, 0x80, 0xFFFF_FF80),
            ("UInt16", "UInt32", 0xFFFF, 0xFFFF, 0xFFFF_FFFF),
            ("UInt16", "UInt64", 0x8000, 0x8000, 0xFFFF_FFFF_FFFF_8000),
            ("UInt32", "UInt64", 0xFFFF_FFFF, 0xFFFF_FFFF, u64::MAX),
            ("UInt16", "UInt8", 0x0100, 0, 1),
            ("UInt16", "UInt8", 0xFFFF, 0xFF, 0),
            ("UInt32", "UInt8", 0xDEAD_BEEF, 0xEF, 0xDE),
            ("UInt32", "UInt16", 0xDEAD_BEEF, 0xBEEF, 0xDEAD),
            ("UInt64", "UInt16", u64::MAX, 0xFFFF, 0),
            ("UInt64", "UInt32", 0x1_0000_0000, 0, 1),
            ("UInt64", "UInt32", u64::MAX, 0xFFFF_FFFF, 0),
        ];
        for &(from, to, a, expected, near_miss) in cases {
            let term = uint_conv(from, to, a);
            let ty = tc
                .infer_type(&term)
                .unwrap_or_else(|e| panic!("{from}.to{to} must type-check: {e:?}"));
            assert!(is_const(&ty, to), "{from}.to{to} : {to}, got {ty:?}");
            assert!(
                tc.is_def_eq(&term, &uint_of(to, expected)),
                "{from}.to{to} {a:#x} must be {expected:#x}"
            );
            assert!(
                !tc.is_def_eq(&term, &uint_of(to, near_miss)),
                "{from}.to{to} {a:#x} = {near_miss:#x} is FALSE in Lean"
            );
        }
        // Round trip: widen-then-narrow is the identity; narrow-then-widen is
        // NOT (it loses the high bits) — the twin that keeps this honest.
        let up_down = Expr::app(
            Expr::const_(Name::from_string("UInt64.toUInt8"), vec![]),
            uint_conv("UInt8", "UInt64", 0xAB),
        );
        assert!(tc.is_def_eq(&up_down, &uint_of("UInt8", 0xAB)));
        let down_up = Expr::app(
            Expr::const_(Name::from_string("UInt8.toUInt64"), vec![]),
            uint_conv("UInt64", "UInt8", 0x1AB),
        );
        assert!(tc.is_def_eq(&down_up, &uint_of("UInt64", 0xAB)));
        assert!(!tc.is_def_eq(&down_up, &uint_of("UInt64", 0x1AB)));
        // `Nat.toUInt8` is Lean's abbreviation for `UInt8.ofNat`, wrap included.
        let nat_to = Expr::app(
            Expr::const_(Name::from_string("Nat.toUInt8"), vec![]),
            Expr::nat_lit(300),
        );
        assert!(tc.is_def_eq(&nat_to, &uint_of("UInt8", 44)));
        assert!(!tc.is_def_eq(&nat_to, &uint_of("UInt8", 255)));
        // No same-width conversion and nothing at USize: neither exists in the
        // source these were transcribed from / the width is opaque.
        for absent in [
            "UInt8.toUInt8",
            "UInt64.toUInt64",
            "USize.toUInt8",
            "UInt8.toUSize",
        ] {
            assert!(
                env.get_const(&Name::from_string(absent)).is_none(),
                "{absent} must not be declared by this overlay"
            );
        }
    }

    /// Same three-way pin as the shifts, for the conversion reducers
    /// (`native_reducers_uint_conv.rs`): `n % 2^M` narrowing, identity widening.
    #[test]
    fn test_uint_conversion_bodies_agree_with_native_reducers() {
        use crate::env::native_reducers_uint_conv as nc;
        type Reducer = fn(&[&Expr]) -> Option<Expr>;
        let table: [(&str, &str, Reducer); 12] = [
            ("UInt16", "UInt8", nc::reduce_uint16_to_uint8),
            ("UInt32", "UInt8", nc::reduce_uint32_to_uint8),
            ("UInt32", "UInt16", nc::reduce_uint32_to_uint16),
            ("UInt64", "UInt8", nc::reduce_uint64_to_uint8),
            ("UInt64", "UInt16", nc::reduce_uint64_to_uint16),
            ("UInt64", "UInt32", nc::reduce_uint64_to_uint32),
            ("UInt8", "UInt16", nc::reduce_uint8_to_uint16),
            ("UInt8", "UInt32", nc::reduce_uint8_to_uint32),
            ("UInt8", "UInt64", nc::reduce_uint8_to_uint64),
            ("UInt16", "UInt32", nc::reduce_uint16_to_uint32),
            ("UInt16", "UInt64", nc::reduce_uint16_to_uint64),
            ("UInt32", "UInt64", nc::reduce_uint32_to_uint64),
        ];
        let bits_of = |c: &str| BIT_WIDTHS.iter().find(|(n, _)| *n == c).expect("known").1;
        let env = Environment::with_prelude();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for (from, to, reducer) in table {
            let (fb, tb) = (bits_of(from), bits_of(to));
            let from_max = max_of(fb);
            for a in [0, 1, 0xFF, 0x100, from_max >> 1, from_max - 1, from_max] {
                let a = a.min(from_max);
                let model = if tb >= 64 { a } else { a % (1u64 << tb) };
                let lit = Expr::nat_lit(a);
                let native =
                    reducer(&[&lit]).unwrap_or_else(|| panic!("{from}.to{to} reducer declined"));
                assert_eq!(
                    native,
                    Expr::nat_lit(model),
                    "NATIVE {from}.to{to} {a:#x} disagrees with Lean"
                );
                let body = uint_to_nat(to, uint_conv(from, to, a));
                assert!(
                    tc.is_def_eq(&body, &Expr::nat_lit(model)),
                    "BODY {from}.to{to} {a:#x} must be {model:#x}"
                );
                assert!(!tc.is_def_eq(&body, &Expr::nat_lit(model ^ 1)));
            }
        }
    }

    /// The width helper fails CLOSED: an unknown carrier is an error, never a
    /// guessed width baked into a shift body.
    #[test]
    fn test_uint_arith_refuses_a_carrier_with_no_fixed_width() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat");
        env.init_uint_types().expect("UInt carriers");
        // (`Nat` would be the wrong third witness: `Nat.shiftLeft` is a real
        // constant of its own, so its presence says nothing about this gate.)
        for bogus in ["USize", "UInt128", "Bool"] {
            let error = env
                .init_one_uint_arith(bogus)
                .expect_err("no fixed width, no machine arithmetic");
            assert!(
                matches!(error, EnvError::UnknownInductive(ref n) if n.to_string() == bogus),
                "unexpected error for {bogus}: {error:?}"
            );
            assert!(
                env.get_const(&Name::from_string(&format!("{bogus}.shiftLeft")))
                    .is_none(),
                "{bogus}.shiftLeft must not have been declared"
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

            for (class, op) in [
                ("HAdd", "add"),
                ("HSub", "sub"),
                ("HMul", "mul"),
                ("HDiv", "div"),
                ("HMod", "mod"),
                ("HAnd", "land"),
                ("HOr", "lor"),
                ("HXor", "xor"),
                ("HShiftLeft", "shiftLeft"),
                ("HShiftRight", "shiftRight"),
            ] {
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
        for op in [
            "add",
            "sub",
            "mul",
            "div",
            "mod",
            "land",
            "lor",
            "xor",
            "shiftLeft",
            "shiftRight",
        ] {
            assert!(
                env.get_const(&Name::from_string(&format!("USize.{op}")))
                    .is_none(),
                "USize.{op} must stay absent until platform width is bound"
            );
        }
        for class in [
            "HAdd",
            "HSub",
            "HMul",
            "HDiv",
            "HMod",
            "HAnd",
            "HOr",
            "HXor",
            "HShiftLeft",
            "HShiftRight",
        ] {
            assert!(
                !env.is_instance(&Name::from_string(&format!("inst{class}USize"))),
                "inst{class}USize must not claim portable fixed-width semantics"
            );
        }
    }
}

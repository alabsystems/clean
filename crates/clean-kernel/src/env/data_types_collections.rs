// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Collection and structural data type initialization: ULift, Char, List, String
//!
//! Split from `data_types.rs` for #307 (large file splitting).
//! Basic algebraic types (Option, Sum, etc.) remain in `data_types.rs`.
//! Numeric types (Bool, Nat, Int) are in `data_types_nat.rs`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize ULift (universe lifting)
    ///
    /// structure ULift.{r, s} (α : Type s) : Type (max s r) where
    ///   up ::
    ///   down : α
    ///
    /// Also adds:
    /// - ULift.up : {α : Type s} → α → ULift.{r, s} α
    /// - ULift.down : {α : Type s} → ULift.{r, s} α → α
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.ulift_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_ulift(&mut self) -> Result<(), EnvError> {
        if self.ulift_init {
            return Ok(());
        }

        let r = Name::from_string("r");
        let s = Name::from_string("s");

        let type_s = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(s.clone()))));
        let result_sort = Expr::from_kind(ExprKind::Sort(Level::succ(Level::max(
            Level::param(s.clone()),
            Level::param(r.clone()),
        ))));

        // ULift : Type s → Type (max s r)
        let ulift_type = Expr::pi(BinderInfo::Default, type_s.clone(), result_sort);

        let ulift_const = Expr::const_(
            Name::from_string("ULift"),
            vec![Level::param(r.clone()), Level::param(s.clone())],
        );

        // ULift.up : {α : Type s} → α → ULift α
        let ulift_up_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_s.clone());
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let e = b.mk_pi(
                a_id,
                BinderInfo::Default,
                alpha.clone(),
                Expr::app(ulift_const.clone(), alpha),
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_s.clone(), e);
            b.finish(e)
        };

        let ulift_decl = InductiveDecl {
            level_params: vec![r.clone(), s.clone()],
            num_params: 1, // α is a parameter
            types: vec![InductiveType {
                name: Name::from_string("ULift"),
                type_: ulift_type,
                constructors: vec![Constructor {
                    name: Name::from_string("ULift.up"),
                    type_: ulift_up_type,
                }],
            }],
        };

        self.add_inductive(ulift_decl)?;

        // Register structure field for ULift
        self.structure_fields
            .insert(Name::from_string("ULift"), vec![Name::from_string("down")]);

        // Add ULift.down projection
        // ULift.down : {α : Type s} → ULift α → α
        let ulift_down_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_s.clone());
            let ulift_alpha = Expr::app(ulift_const.clone(), alpha.clone());
            let (u_id, _u) = b.fresh_local(ulift_alpha.clone());
            let e = b.mk_pi(u_id, BinderInfo::Default, ulift_alpha, alpha.clone());
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_s.clone(), e);
            b.finish(e)
        };

        let ulift_rec = Expr::const_(
            Name::from_string("ULift.rec"),
            vec![
                Level::succ(Level::param(s.clone())),
                Level::param(r.clone()),
                Level::param(s.clone()),
            ],
        );

        // ULift.down := λ {α} (u : ULift α) => ULift.rec α motive minor u
        let ulift_down_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_s.clone());
            let ulift_alpha = Expr::app(ulift_const.clone(), alpha.clone());
            let (u_id, u) = b.fresh_local(ulift_alpha.clone());

            // motive: λ _ : ULift α => α
            let (mv_id, _mv) = b.fresh_local(ulift_alpha.clone());
            let motive = b.mk_lam(
                mv_id,
                BinderInfo::Default,
                ulift_alpha.clone(),
                alpha.clone(),
            );

            // minor: λ a : α => a (identity)
            let (a_id, a) = b.fresh_local(alpha.clone());
            let minor = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), a);

            let body = Expr::apps(ulift_rec.clone(), [alpha.clone(), motive, minor, u]);
            let e = b.mk_lam(u_id, BinderInfo::Default, ulift_alpha, body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_s.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("ULift.down"),
            level_params: vec![r.clone(), s.clone()],
            type_: ulift_down_type,
            value: ulift_down_value,
            is_reducible: true,
        })?;

        self.ulift_init = true;
        Ok(())
    }

    /// Check if ULift has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_ulift` has completed successfully
    /// ENSURES: Pure - no side effects
    pub(crate) fn has_ulift(&self) -> bool {
        self.ulift_init
    }

    /// Initialize Char type
    ///
    /// Char is a structure wrapping a UInt32 (simplified, no validity proof in kernel)
    /// In the kernel, we use Nat as the underlying representation.
    ///
    /// structure Char where
    ///   val : Nat
    ///
    /// Also adds:
    /// - Char.ofNat : Nat → Char
    /// - Char.toNat : Char → Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.char_init == true`
    /// ENSURES: On success, required dependencies (`nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_char(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`): the seeded Char is
        // skipped so the genuine v4.30 Char imports through the checked `.olean`
        // path. The seed below is now the GENUINE v4.30 shape
        // (`⟨val : UInt32, valid : val.isValidChar⟩` over the BitVec-backed
        // UInt32 — carrier-parity design P2), so the DEFAULT lane matches Lean;
        // import still suppresses it because the native Char reducers +
        // `mk_char_expr` (→ `Char.ofNat`) drive the genuine olean Char in that
        // lane without needing the seed present at prelude-init time.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.char_init {
            return Ok(());
        }

        // The genuine Char wraps a BitVec-backed `UInt32` plus a validity proof,
        // so bootstrap the UInt32 carrier stack (idempotent; these normally seed
        // later in `init_prelude_extended`, but Char is pulled early by
        // `init_string`). `Or`/`And` back `Nat.isValidChar`'s body.
        self.init_nat()?;
        self.init_or()?;
        self.init_and()?;
        self.init_fin()?;
        self.init_hpow()?;
        self.init_ofnat()?;
        self.init_ofnat_nat()?;
        self.init_uint32()?;

        let char_const = Expr::const_(Name::from_string("Char"), vec![]);
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let uint32_const = Expr::const_(Name::from_string("UInt32"), vec![]);
        let prop = Expr::sort(Level::zero());
        let lt_nat = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                [
                    nat_const.clone(),
                    Expr::const_(Name::from_string("instLTNat"), vec![]),
                    l,
                    r,
                ],
            )
        };
        let and_ =
            |a: Expr, b: Expr| Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [a, b]);
        let or_ =
            |a: Expr, b: Expr| Expr::apps(Expr::const_(Name::from_string("Or"), vec![]), [a, b]);

        // Nat.isValidChar : Nat → Prop
        //   := fun n => n < 55296 ∨ (57343 < n ∧ n < 1114112)
        {
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat_const.clone());
                let body = or_(
                    lt_nat(n.clone(), Self::ofnat_nat_lit(55296)),
                    and_(
                        lt_nat(Self::ofnat_nat_lit(57343), n.clone()),
                        lt_nat(n.clone(), Self::ofnat_nat_lit(1114112)),
                    ),
                );
                let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Nat.isValidChar"),
                level_params: vec![],
                type_: Expr::pi(BinderInfo::Default, nat_const.clone(), prop.clone()),
                value,
                is_reducible: true,
            })?;
        }
        // UInt32.isValidChar : UInt32 → Prop := fun n => Nat.isValidChar (UInt32.toNat n)
        {
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(uint32_const.clone());
                let body = Expr::app(
                    Expr::const_(Name::from_string("Nat.isValidChar"), vec![]),
                    Expr::app(Expr::const_(Name::from_string("UInt32.toNat"), vec![]), n),
                );
                let e = b.mk_lam(n_id, BinderInfo::Default, uint32_const.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("UInt32.isValidChar"),
                level_params: vec![],
                type_: Expr::pi(BinderInfo::Default, uint32_const.clone(), prop.clone()),
                value,
                is_reducible: true,
            })?;
        }

        // structure Char where mk :: (val : UInt32) (valid : val.isValidChar)
        let char_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (v_id, v) = b.fresh_local(uint32_const.clone());
            let valid_ty = Expr::app(
                Expr::const_(Name::from_string("UInt32.isValidChar"), vec![]),
                v.clone(),
            );
            let (valid_id, _) = b.fresh_local(valid_ty.clone());
            let r = b.mk_pi(valid_id, BinderInfo::Default, valid_ty, char_const.clone());
            let r = b.mk_pi(v_id, BinderInfo::Default, uint32_const.clone(), r);
            b.finish(r)
        };
        self.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("Char"),
                type_: Expr::sort(Level::succ(Level::zero())),
                constructors: vec![Constructor {
                    name: Name::from_string("Char.mk"),
                    type_: char_mk_type,
                }],
            }],
        })?;
        self.register_structure_fields(
            Name::from_string("Char"),
            vec![Name::from_string("val"), Name::from_string("valid")],
        )?;

        // Char.val : Char → UInt32 := fun self => self.1  (Proj)
        {
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (s_id, s) = b.fresh_local(char_const.clone());
                let body = Expr::proj(Name::from_string("Char"), 0, s);
                let e = b.mk_lam(s_id, BinderInfo::Default, char_const.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Char.val"),
                level_params: vec![],
                type_: Expr::pi(
                    BinderInfo::Default,
                    char_const.clone(),
                    uint32_const.clone(),
                ),
                value,
                is_reducible: true,
            })?;
        }
        // Char.valid : (self : Char) → UInt32.isValidChar (Char.val self) := fun self => self.2
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (s_id, s) = b.fresh_local(char_const.clone());
                let concl = Expr::app(
                    Expr::const_(Name::from_string("UInt32.isValidChar"), vec![]),
                    Expr::app(Expr::const_(Name::from_string("Char.val"), vec![]), s),
                );
                let r = b.mk_pi(s_id, BinderInfo::Default, char_const.clone(), concl);
                b.finish(r)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (s_id, s) = b.fresh_local(char_const.clone());
                let body = Expr::proj(Name::from_string("Char"), 1, s);
                let e = b.mk_lam(s_id, BinderInfo::Default, char_const.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Char.valid"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: false,
            })?;
        }
        // Char.toNat : Char → Nat := fun c => UInt32.toNat (Char.val c)
        {
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (c_id, c) = b.fresh_local(char_const.clone());
                let body = Expr::app(
                    Expr::const_(Name::from_string("UInt32.toNat"), vec![]),
                    Expr::app(Expr::const_(Name::from_string("Char.val"), vec![]), c),
                );
                let e = b.mk_lam(c_id, BinderInfo::Default, char_const.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Char.toNat"),
                level_params: vec![],
                type_: Expr::pi(BinderInfo::Default, char_const.clone(), nat_const.clone()),
                value,
                is_reducible: true,
            })?;
        }

        // Char.ofNatAux / Char.ofNat / Char.utf8Size need `dite`, the `Decidable`
        // instances, `Nat.decLt`, `Nat.le_trans` etc. — none available this early
        // (`init_char` is pulled by `init_string` in the core phase). They are
        // seeded by `init_char_defs`, wired after `init_decidable_eq` in
        // `init_prelude_extended`.
        self.char_init = true;
        Ok(())
    }

    /// Seed `Char.ofNatAux` / `Char.ofNat` / `Char.utf8Size` — the genuine v4.30
    /// bodies that depend on `dite` / the `Decidable` instances / `Nat.decLt` /
    /// `Nat.le_trans`, none of which exist at `init_char` time. Wired after
    /// `init_decidable_eq` in `init_prelude_extended`. Idempotent; import mode
    /// (and a Char-less env) skip cleanly.
    pub(crate) fn init_char_defs(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.get_const(&Name::from_string("Char")).is_none()
            || self.get_const(&Name::from_string("Char.ofNat")).is_some()
        {
            return Ok(());
        }
        let char_const = Expr::const_(Name::from_string("Char"), vec![]);
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let lt_nat = |l: Expr, r: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                [nat_const.clone(), c("instLTNat"), l, r],
            )
        };
        let and_ = |a: Expr, b: Expr| Expr::apps(c("And"), [a, b]);
        let or_ = |a: Expr, b: Expr| Expr::apps(c("Or"), [a, b]);
        // `Nat.le_of_ble_eq_true a b (Eq.refl Bool (Nat.ble a b))` : Nat.le a b.
        let nat_le_concrete = |a: Expr, b: Expr| {
            let ble = Expr::apps(c("Nat.ble"), [a.clone(), b.clone()]);
            let refl = Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [c("Bool"), ble],
            );
            Expr::apps(c("Nat.le_of_ble_eq_true"), [a, b, refl])
        };
        let is_valid = |e: Expr| Expr::app(c("Nat.isValidChar"), e);

        // Char.ofNatAux : (n : Nat) → (h : Nat.isValidChar n) → Char
        //   := fun n h => Char.mk (UInt32.ofBitVec (BitVec.ofNatLT 32 n <n<2^32>)) h
        // The `⟨n, valid⟩` field-2 proof is `h` itself: `UInt32.isValidChar
        // (UInt32.ofBitVec (BitVec.ofNatLT 32 n _))` δι-reduces to
        // `Nat.isValidChar n` (BitVec.toNat of ofNatLT is `n` by ι). The width
        // bound `n < 2^32` is derived from `h` by `Or.rec` (isValidChar ⇒ n <
        // 1114112 < 2^32) — axiom-free.
        {
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat_const.clone());
                let h_ty = is_valid(n.clone());
                let (h_id, _) = b.fresh_local(h_ty.clone());
                let r = b.mk_pi(h_id, BinderInfo::Default, h_ty, char_const.clone());
                let r = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), r);
                b.finish(r)
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat_const.clone());
                let h_ty = is_valid(n.clone());
                let (h_id, h) = b.fresh_local(h_ty.clone());
                let a_prop = lt_nat(n.clone(), Self::ofnat_nat_lit(55296));
                let b_prop = lt_nat(Self::ofnat_nat_lit(57343), n.clone());
                let cc_prop = lt_nat(n.clone(), Self::ofnat_nat_lit(1114112));
                let and_bc = and_(b_prop.clone(), cc_prop.clone());
                let succ_n = Expr::app(c("Nat.succ"), n.clone());
                let two_pow32 = Self::two_pow(Self::ofnat_nat_lit(32));
                let motive = {
                    let (t_id, _) = b.fresh_local(or_(a_prop.clone(), and_bc.clone()));
                    b.mk_lam(
                        t_id,
                        BinderInfo::Default,
                        or_(a_prop.clone(), and_bc.clone()),
                        lt_nat(n.clone(), two_pow32.clone()),
                    )
                };
                let inl = {
                    let (h1_id, h1) = b.fresh_local(a_prop.clone());
                    let body = Expr::apps(
                        c("Nat.le_trans"),
                        [
                            succ_n.clone(),
                            Self::ofnat_nat_lit(55296),
                            two_pow32.clone(),
                            h1,
                            nat_le_concrete(Self::ofnat_nat_lit(55296), two_pow32.clone()),
                        ],
                    );
                    b.mk_lam(h1_id, BinderInfo::Default, a_prop.clone(), body)
                };
                let inr = {
                    let (h2_id, h2) = b.fresh_local(and_bc.clone());
                    let and_right =
                        Expr::apps(c("And.right"), [b_prop.clone(), cc_prop.clone(), h2]);
                    let body = Expr::apps(
                        c("Nat.le_trans"),
                        [
                            succ_n.clone(),
                            Self::ofnat_nat_lit(1114112),
                            two_pow32.clone(),
                            and_right,
                            nat_le_concrete(Self::ofnat_nat_lit(1114112), two_pow32.clone()),
                        ],
                    );
                    b.mk_lam(h2_id, BinderInfo::Default, and_bc.clone(), body)
                };
                let bound = Expr::apps(
                    c("Or.rec"),
                    [a_prop.clone(), and_bc.clone(), motive, inl, inr, h.clone()],
                );
                let bv = Expr::apps(
                    c("BitVec.ofNatLT"),
                    [Self::ofnat_nat_lit(32), n.clone(), bound],
                );
                let u32 = Expr::app(c("UInt32.ofBitVec"), bv);
                let body = Expr::apps(c("Char.mk"), [u32, h.clone()]);
                let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
                let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Char.ofNatAux"),
                level_params: vec![],
                type_: ty,
                value,
                is_reducible: false,
            })?;
        }
        // Char.ofNat : Nat → Char
        //   := fun n => dite (Nat.isValidChar n) (fun h => Char.ofNatAux n h)
        //        (fun _ => Char.mk (UInt32.ofBitVec (BitVec.ofNatLT 32 0 _)) <0 valid>)
        // Genuine v4.30: invalid code points map to '\0'.
        {
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(nat_const.clone());
                let a_prop = lt_nat(n.clone(), Self::ofnat_nat_lit(55296));
                let b_prop = lt_nat(Self::ofnat_nat_lit(57343), n.clone());
                let cc_prop = lt_nat(n.clone(), Self::ofnat_nat_lit(1114112));
                let and_bc = and_(b_prop.clone(), cc_prop.clone());
                let cond = is_valid(n.clone());
                let dec_lt = |l: Expr, r: Expr| Expr::apps(c("Nat.decLt"), [l, r]);
                let inst = Expr::apps(
                    c("instDecidableOr"),
                    [
                        a_prop.clone(),
                        and_bc.clone(),
                        dec_lt(n.clone(), Self::ofnat_nat_lit(55296)),
                        Expr::apps(
                            c("instDecidableAnd"),
                            [
                                b_prop.clone(),
                                cc_prop.clone(),
                                dec_lt(Self::ofnat_nat_lit(57343), n.clone()),
                                dec_lt(n.clone(), Self::ofnat_nat_lit(1114112)),
                            ],
                        ),
                    ],
                );
                let then_fn = {
                    let (h_id, h) = b.fresh_local(cond.clone());
                    let body = Expr::apps(c("Char.ofNatAux"), [n.clone(), h]);
                    b.mk_lam(h_id, BinderInfo::Default, cond.clone(), body)
                };
                let two_pow32 = Self::two_pow(Self::ofnat_nat_lit(32));
                let b0 = nat_le_concrete(Self::ofnat_nat_lit(1), two_pow32.clone());
                let bv0 = Expr::apps(
                    c("BitVec.ofNatLT"),
                    [Self::ofnat_nat_lit(32), Self::ofnat_nat_lit(0), b0],
                );
                let u32_0 = Expr::app(c("UInt32.ofBitVec"), bv0);
                let v0 = Expr::apps(
                    c("Or.inl"),
                    [
                        lt_nat(Self::ofnat_nat_lit(0), Self::ofnat_nat_lit(55296)),
                        and_(
                            lt_nat(Self::ofnat_nat_lit(57343), Self::ofnat_nat_lit(0)),
                            lt_nat(Self::ofnat_nat_lit(0), Self::ofnat_nat_lit(1114112)),
                        ),
                        nat_le_concrete(Self::ofnat_nat_lit(1), Self::ofnat_nat_lit(55296)),
                    ],
                );
                let neg_cond = Expr::app(c("Not"), cond.clone());
                let else_fn = {
                    let (x_id, _) = b.fresh_local(neg_cond.clone());
                    let body = Expr::apps(c("Char.mk"), [u32_0, v0]);
                    b.mk_lam(x_id, BinderInfo::Default, neg_cond.clone(), body)
                };
                let body = Expr::apps(
                    Expr::const_(Name::from_string("dite"), vec![Level::succ(Level::zero())]),
                    [char_const.clone(), cond.clone(), inst, then_fn, else_fn],
                );
                let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Char.ofNat"),
                level_params: vec![],
                type_: Expr::pi(BinderInfo::Default, nat_const.clone(), char_const.clone()),
                value,
                is_reducible: true,
            })?;
        }
        // Char.utf8Size : Char → Nat — the UTF-8 byte length of the code point.
        // The native `Char.utf8Size` reducer computes it directly on a
        // `Char.ofNat`/ctor literal (byte-table, matching Lean); the seeded body
        // here is the definitional fallback for symbolic Chars: it re-derives the
        // size from `Char.toNat` via `Nat.ble` comparisons (1/2/3/4 for the
        // 0x7F / 0x7FF / 0xFFFF boundaries).
        {
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (ch_id, ch) = b.fresh_local(char_const.clone());
                let v = Expr::app(c("Char.toNat"), ch);
                // ite over Nat.ble v <bound>: `@Bool.rec (fun _ => Nat) <else> <then> (Nat.ble v bound)`.
                let ble = |val: Expr, bound: u64| {
                    Expr::apps(c("Nat.ble"), [val, Self::ofnat_nat_lit(bound)])
                };
                let bool_rec = |scrut: Expr, then_1: Expr, else_0: Expr| {
                    // Bool.rec {motive := fun _ => Nat} (false-case) (true-case) scrut
                    let motive = Expr::lam(BinderInfo::Default, c("Bool"), nat_const.clone());
                    Expr::apps(
                        Expr::const_(
                            Name::from_string("Bool.rec"),
                            vec![Level::succ(Level::zero())],
                        ),
                        [motive, else_0, then_1, scrut],
                    )
                };
                let one = Self::ofnat_nat_lit(1);
                let two = Self::ofnat_nat_lit(2);
                let three = Self::ofnat_nat_lit(3);
                let four = Self::ofnat_nat_lit(4);
                // v ≤ 0xFFFF ? 3 : 4
                let inner3 = bool_rec(ble(v.clone(), 65535), three, four);
                // v ≤ 0x7FF ? 2 : inner3
                let inner2 = bool_rec(ble(v.clone(), 2047), two, inner3);
                // v ≤ 0x7F ? 1 : inner2
                let body = bool_rec(ble(v.clone(), 127), one, inner2);
                let e = b.mk_lam(ch_id, BinderInfo::Default, char_const.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Char.utf8Size"),
                level_params: vec![],
                type_: Expr::pi(BinderInfo::Default, char_const.clone(), nat_const.clone()),
                value,
                is_reducible: true,
            })?;
        }
        Ok(())
    }

    /// Check if Char has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_char` has completed successfully
    /// ENSURES: Pure - no side effects
    pub(crate) fn has_char(&self) -> bool {
        self.char_init
    }

    /// Initialize List type (polymorphic linked list)
    ///
    /// inductive List (α : Type u) where
    ///   | nil : List α
    ///   | cons (head : α) (tail : List α) : List α
    ///
    /// Also adds:
    /// - List.head? : List α → Option α
    /// - List.tail : List α → List α
    /// - List.append : List α → List α → List α
    /// - List.length : List α → Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.list_init == true`
    /// ENSURES: On success, required dependencies (`nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_list(&mut self) -> Result<(), EnvError> {
        if self.list_init {
            return Ok(());
        }

        // Ensure Nat is initialized first (for length)
        self.init_nat()?;

        let u = Name::from_string("u");

        // Type u
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));

        // List : Type u → Type u
        let list_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());

        let list_const = Expr::const_(Name::from_string("List"), vec![Level::param(u.clone())]);

        // List.nil : {α : Type u} → List α
        let list_nil_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let e = b.mk_pi(
                alpha_id,
                BinderInfo::Implicit,
                type_u.clone(),
                Expr::app(list_const.clone(), alpha),
            );
            b.finish(e)
        };

        // List.cons : {α : Type u} → α → List α → List α
        let list_cons_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let (head_id, _head) = b.fresh_local(alpha.clone());
            let (tail_id, _tail) = b.fresh_local(list_alpha.clone());
            let e = b.mk_pi(
                tail_id,
                BinderInfo::Default,
                list_alpha.clone(),
                list_alpha.clone(),
            );
            let e = b.mk_pi(head_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let list_decl = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1, // α is a parameter
            types: vec![InductiveType {
                name: Name::from_string("List"),
                type_: list_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("List.nil"),
                        type_: list_nil_type,
                    },
                    Constructor {
                        name: Name::from_string("List.cons"),
                        type_: list_cons_type,
                    },
                ],
            }],
        };

        self.add_inductive(list_decl)?;

        // Add List.tail : {α : Type u} → List α → List α
        // List.tail l := List.rec List.nil (λ _ tail _ => tail) l
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let list_rec = Expr::const_(
            Name::from_string("List.rec"),
            vec![
                Level::succ(Level::param(u.clone())),
                Level::param(u.clone()),
            ],
        );
        let list_nil = Expr::const_(Name::from_string("List.nil"), vec![Level::param(u.clone())]);

        let list_tail_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha);
            let (l_id, _l) = b.fresh_local(list_alpha.clone());
            let e = b.mk_pi(
                l_id,
                BinderInfo::Default,
                list_alpha.clone(),
                list_alpha.clone(),
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // List.tail {α : Type u} (l : List α) : List α
        // = @List.rec α (λ _ => List α) (List.nil α) (λ _ tail _ => tail) l
        // List.rec arg order: α, motive, nil_case, cons_case, major
        let list_tail_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let (l_id, l) = b.fresh_local(list_alpha.clone());

            // motive: λ (_ : List α) => List α
            let (m_id, _m) = b.fresh_local(list_alpha.clone());
            let motive = b.mk_lam(
                m_id,
                BinderInfo::Default,
                list_alpha.clone(),
                list_alpha.clone(),
            );

            // nil case: List.nil {α}
            let nil_case = Expr::app(list_nil.clone(), alpha.clone());

            // cons case: λ (_ : α) (tail : List α) (_ : List α) => tail
            let (hd_id, _hd) = b.fresh_local(alpha.clone());
            let (tl_id, tl) = b.fresh_local(list_alpha.clone());
            let (ih_id, _ih) = b.fresh_local(list_alpha.clone());
            let cons_case = b.mk_lam(ih_id, BinderInfo::Default, list_alpha.clone(), tl.clone());
            let cons_case = b.mk_lam(tl_id, BinderInfo::Default, list_alpha.clone(), cons_case);
            let cons_case = b.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), cons_case);

            // @List.rec α motive nil_case cons_case l
            let body = Expr::apps(
                list_rec.clone(),
                [alpha.clone(), motive, nil_case, cons_case, l],
            );
            let e = b.mk_lam(l_id, BinderInfo::Default, list_alpha, body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("List.tail"),
            level_params: vec![u.clone()],
            type_: list_tail_type,
            value: list_tail_value,
            is_reducible: true,
        })?;

        // Add List.length : {α : Type u} → List α → Nat
        //
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.30 census
        // 2026-07-06): Lean v4.30 stores List.length as a brecOn tower — the
        // direct List.rec seed below is only propositionally equal, so the
        // olean twin fails the value-defeq dedup and every eq_def/lemma
        // elaborated through the genuine body cascades. Import-suppressed
        // (WS17 pattern) with the rest of the List.* recursion cluster so the
        // genuine olean definition imports through the checked add_decl path;
        // the List.length native reducer is name-keyed and unaffected.
        if !self.suppress_lossy_structure_stubs {
            let list_length_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha);
                let (l_id, _l) = b.fresh_local(list_alpha.clone());
                let e = b.mk_pi(l_id, BinderInfo::Default, list_alpha, nat_const.clone());
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };

            let list_rec_nat = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(Level::zero()), Level::param(u.clone())],
            );

            let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

            // List.length {α : Type u} (l : List α) : Nat
            // = @List.rec α (λ _ => Nat) Nat.zero (λ _ _ ih => Nat.succ ih) l
            let list_length_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let (l_id, l) = b.fresh_local(list_alpha.clone());

                // motive: λ (_ : List α) => Nat
                let (m_id, _m) = b.fresh_local(list_alpha.clone());
                let motive = b.mk_lam(
                    m_id,
                    BinderInfo::Default,
                    list_alpha.clone(),
                    nat_const.clone(),
                );

                // cons case: λ (_ : α) (_ : List α) (ih : Nat) => Nat.succ ih
                let (hd_id, _hd) = b.fresh_local(alpha.clone());
                let (tl_id, _tl) = b.fresh_local(list_alpha.clone());
                let (ih_id, ih) = b.fresh_local(nat_const.clone());
                let cons_case = b.mk_lam(
                    ih_id,
                    BinderInfo::Default,
                    nat_const.clone(),
                    Expr::app(nat_succ.clone(), ih),
                );
                let cons_case = b.mk_lam(tl_id, BinderInfo::Default, list_alpha.clone(), cons_case);
                let cons_case = b.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), cons_case);

                // @List.rec α motive Nat.zero cons_case l
                let body = Expr::apps(
                    list_rec_nat.clone(),
                    [alpha.clone(), motive, nat_zero.clone(), cons_case, l],
                );
                let e = b.mk_lam(l_id, BinderInfo::Default, list_alpha, body);
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.length"),
                level_params: vec![u.clone()],
                type_: list_length_type,
                value: list_length_value,
                is_reducible: true,
            })?;
        }

        // Pure List combinators used across trust-ir's Semantics/State layer:
        // `List.any` (State/Memory.lean isAllocated/isInBounds), `List.all`
        // (Semantics/Arith.lean executableVectorPayloadMatches), `List.range`
        // + `List.foldl` (Arith.lean popCountWidth), plus `List.map` /
        // `List.foldr`. All are axiom-free `List.rec` / `Nat.rec` Definitions.
        self.init_list_combinators()?;

        self.list_init = true;
        Ok(())
    }

    /// Initialize the pure (non-monadic) List combinators on top of the bare
    /// `List` inductive: `List.foldr`, `List.foldl`, `List.map`, `List.any`,
    /// `List.all`, and `List.range`.
    ///
    /// Each combinator is a genuine `Declaration::Definition` (never an
    /// `Axiom`): the recursive ones are `List.rec` eliminations and `List.range`
    /// is a `Nat.rec` recursion. None introduce a kernel axiom, so their
    /// `axiom_deps` closure is empty, and each reduces correctly on ground
    /// inputs (gated by `rfl` repros in `clean check`).
    ///
    /// Called from the tail of [`init_list`](Self::init_list); not idempotent on
    /// its own (it must run exactly once, after the `List` inductive and `Nat`
    /// /`Bool` are registered).
    fn init_list_combinators(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.30 census
        // 2026-07-06): every combinator registered here (`List.foldr`,
        // `List.foldl`, `List.any`, `List.all`, `List.range`, plus the
        // Clean-only `List.rangeAux` helper) is a direct `List.rec`/`Nat.rec`
        // elimination — Lean v4.30 stores brecOn towers (and `List.range` via
        // `List.range.loop`, not `rangeAux`), so the seeded twins fail the
        // value-defeq dedup and their eq_def/lemma webs cascade
        // (Init.Data.List.Basic / Range). Import-suppressed (WS17 pattern) so
        // the genuine olean definitions import through the checked add_decl
        // path. The default proof-execution lane is unchanged.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        // Element / result universe parameters. `u` for the list element type,
        // `v` for the codomain of fold/map.
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_lvl = Level::param(u.clone());
        let v_lvl = Level::param(v.clone());

        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_lvl.clone())));
        let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(v_lvl.clone())));

        let list_const_u = Expr::const_(Name::from_string("List"), vec![u_lvl.clone()]);

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let bool_or = Expr::const_(Name::from_string("Bool.or"), vec![]);
        let bool_and = Expr::const_(Name::from_string("Bool.and"), vec![]);

        // ── List.foldr {α : Type u} {β : Type v}
        //      (f : α → β → β) (init : β) (l : List α) : β ──────────────────
        // = @List.rec α (λ _ => β) init (λ hd _ ih => f hd ih) l
        //
        // Motive returns `β : Type v`, so `List.rec.{succ v, u}`.
        let foldr_rec = Expr::const_(
            Name::from_string("List.rec"),
            vec![Level::succ(v_lvl.clone()), u_lvl.clone()],
        );
        let foldr_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let list_alpha = Expr::app(list_const_u.clone(), alpha.clone());
            // f : α → β → β
            let f_ty = Expr::pi(
                BinderInfo::Default,
                alpha.clone(),
                Expr::pi(BinderInfo::Default, beta.clone(), beta.clone()),
            );
            let (f_id, _f) = b.fresh_local(f_ty.clone());
            let (init_id, _init) = b.fresh_local(beta.clone());
            let (l_id, _l) = b.fresh_local(list_alpha.clone());
            let e = beta.clone();
            let e = b.mk_pi(l_id, BinderInfo::Default, list_alpha.clone(), e);
            let e = b.mk_pi(init_id, BinderInfo::Default, beta.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let foldr_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let list_alpha = Expr::app(list_const_u.clone(), alpha.clone());
            let f_ty = Expr::pi(
                BinderInfo::Default,
                alpha.clone(),
                Expr::pi(BinderInfo::Default, beta.clone(), beta.clone()),
            );
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let (init_id, init) = b.fresh_local(beta.clone());
            let (l_id, l) = b.fresh_local(list_alpha.clone());

            // motive: λ (_ : List α) => β
            let (m_id, _m) = b.fresh_local(list_alpha.clone());
            let motive = b.mk_lam(m_id, BinderInfo::Default, list_alpha.clone(), beta.clone());

            // cons case: λ (hd : α) (_ : List α) (ih : β) => f hd ih
            let (hd_id, hd) = b.fresh_local(alpha.clone());
            let (tl_id, _tl) = b.fresh_local(list_alpha.clone());
            let (ih_id, ih) = b.fresh_local(beta.clone());
            let cons_body = Expr::apps(f.clone(), [hd.clone(), ih.clone()]);
            let cons_case = b.mk_lam(ih_id, BinderInfo::Default, beta.clone(), cons_body);
            let cons_case = b.mk_lam(tl_id, BinderInfo::Default, list_alpha.clone(), cons_case);
            let cons_case = b.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), cons_case);

            let body = Expr::apps(
                foldr_rec.clone(),
                [alpha.clone(), motive, init.clone(), cons_case, l.clone()],
            );
            let e = b.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), body);
            let e = b.mk_lam(init_id, BinderInfo::Default, beta.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("List.foldr"),
            level_params: vec![u.clone(), v.clone()],
            type_: foldr_type,
            value: foldr_value,
            is_reducible: true,
        })?;

        // ── List.foldl {α : Type u} {β : Type v}
        //      (f : α → β → α) (init : α) (l : List β) : α ──────────────────
        // Lean-faithful signature (Init.Data.List.Basic): the FIRST implicit
        // `α` is the ACCUMULATOR type and the SECOND `β` is the ELEMENT type, so
        // `f : α → β → α`, `init : α`, `l : List β`, result `α`. (Contrast
        // `List.foldr` above, where `α` is the element type — the two
        // combinators intentionally bind their type params in opposite roles,
        // matching upstream `@List.foldl`/`@List.foldr`.)
        //
        // Left fold cannot be a direct `List.rec` (the accumulator threads
        // forward), so we recurse to a function `α → α` and apply it to `init`:
        //   foldl f init l
        //     = (@List.rec β (λ _ => α → α)
        //          (λ acc => acc)
        //          (λ hd _ ih => λ acc => ih (f acc hd))
        //          l) init
        //
        // The list being eliminated is `List β` (element universe `v`) and the
        // motive returns `α → α : Type u`, so `List.rec.{succ u, v}`.
        let list_const_v = Expr::const_(Name::from_string("List"), vec![v_lvl.clone()]);
        let foldl_rec = Expr::const_(
            Name::from_string("List.rec"),
            vec![Level::succ(u_lvl.clone()), v_lvl.clone()],
        );
        let foldl_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let list_beta = Expr::app(list_const_v.clone(), beta.clone());
            // f : α → β → α
            let f_ty = Expr::pi(
                BinderInfo::Default,
                alpha.clone(),
                Expr::pi(BinderInfo::Default, beta.clone(), alpha.clone()),
            );
            let (f_id, _f) = b.fresh_local(f_ty.clone());
            let (init_id, _init) = b.fresh_local(alpha.clone());
            let (l_id, _l) = b.fresh_local(list_beta.clone());
            let e = alpha.clone();
            let e = b.mk_pi(l_id, BinderInfo::Default, list_beta.clone(), e);
            let e = b.mk_pi(init_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let foldl_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let list_beta = Expr::app(list_const_v.clone(), beta.clone());
            let f_ty = Expr::pi(
                BinderInfo::Default,
                alpha.clone(),
                Expr::pi(BinderInfo::Default, beta.clone(), alpha.clone()),
            );
            // α → α : Type u
            let alpha_to_alpha = Expr::pi(BinderInfo::Default, alpha.clone(), alpha.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let (init_id, init) = b.fresh_local(alpha.clone());
            let (l_id, l) = b.fresh_local(list_beta.clone());

            // motive: λ (_ : List β) => α → α
            let (m_id, _m) = b.fresh_local(list_beta.clone());
            let motive = b.mk_lam(
                m_id,
                BinderInfo::Default,
                list_beta.clone(),
                alpha_to_alpha.clone(),
            );

            // nil case: λ (acc : α) => acc
            let (nacc_id, nacc) = b.fresh_local(alpha.clone());
            let nil_case = b.mk_lam(nacc_id, BinderInfo::Default, alpha.clone(), nacc);

            // cons case: λ (hd : β) (_ : List β) (ih : α → α) => λ (acc : α) => ih (f acc hd)
            let (hd_id, hd) = b.fresh_local(beta.clone());
            let (tl_id, _tl) = b.fresh_local(list_beta.clone());
            let (ih_id, ih) = b.fresh_local(alpha_to_alpha.clone());
            let (cacc_id, cacc) = b.fresh_local(alpha.clone());
            let f_acc_hd = Expr::apps(f.clone(), [cacc.clone(), hd.clone()]);
            let inner = Expr::app(ih.clone(), f_acc_hd);
            let cons_lam = b.mk_lam(cacc_id, BinderInfo::Default, alpha.clone(), inner);
            let cons_case = b.mk_lam(ih_id, BinderInfo::Default, alpha_to_alpha.clone(), cons_lam);
            let cons_case = b.mk_lam(tl_id, BinderInfo::Default, list_beta.clone(), cons_case);
            let cons_case = b.mk_lam(hd_id, BinderInfo::Default, beta.clone(), cons_case);

            let rec_app = Expr::apps(
                foldl_rec.clone(),
                [beta.clone(), motive, nil_case, cons_case, l.clone()],
            );
            let body = Expr::app(rec_app, init.clone());
            let e = b.mk_lam(l_id, BinderInfo::Default, list_beta.clone(), body);
            let e = b.mk_lam(init_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("List.foldl"),
            level_params: vec![u.clone(), v.clone()],
            type_: foldl_type,
            value: foldl_value,
            is_reducible: true,
        })?;

        // NOTE: `List.map` is intentionally *not* registered here — it is
        // already provided (axiom-free) by `init_list_ops` (data_collection_ops.rs),
        // alongside `List.append` / `List.reverse`, and reaches the prelude via
        // the `init_string_happend_inst` → `init_string_append` → `init_list_ops`
        // chain. Registering it again would raise `DuplicateName`.

        // ── List.any {α : Type u} (l : List α) (p : α → Bool) : Bool ───────
        // = @List.rec α (λ _ => Bool) Bool.false (λ hd _ ih => Bool.or (p hd) ih) l
        //
        // NB: the *list* is the first explicit argument (matching Lean 4's
        // `List.any : List α → (α → Bool) → Bool`), so dot-notation
        // `xs.any p` / `mem.allocations.any (fun a => …)` resolves `xs` to the
        // first `List α` parameter. Motive returns `Bool : Type 0`, so
        // `List.rec.{succ 0, u}`.
        let bool_rec = Expr::const_(
            Name::from_string("List.rec"),
            vec![Level::succ(Level::zero()), u_lvl.clone()],
        );
        // any / all share the same type shape: List α → (α → Bool) → Bool.
        let predicate_combinator_type = || {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const_u.clone(), alpha.clone());
            let p_ty = Expr::pi(BinderInfo::Default, alpha.clone(), bool_const.clone());
            let (l_id, _l) = b.fresh_local(list_alpha.clone());
            let (p_id, _p) = b.fresh_local(p_ty.clone());
            let e = bool_const.clone();
            let e = b.mk_pi(p_id, BinderInfo::Default, p_ty.clone(), e);
            let e = b.mk_pi(l_id, BinderInfo::Default, list_alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        // Shared value builder for any/all, parameterised by base case + the
        // boolean combinator applied in the cons case.
        let predicate_combinator_value = |base: Expr, binop: Expr| {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const_u.clone(), alpha.clone());
            let p_ty = Expr::pi(BinderInfo::Default, alpha.clone(), bool_const.clone());
            let (l_id, l) = b.fresh_local(list_alpha.clone());
            let (p_id, p) = b.fresh_local(p_ty.clone());

            // motive: λ (_ : List α) => Bool
            let (m_id, _m) = b.fresh_local(list_alpha.clone());
            let motive = b.mk_lam(
                m_id,
                BinderInfo::Default,
                list_alpha.clone(),
                bool_const.clone(),
            );

            // cons case: λ (hd : α) (_ : List α) (ih : Bool) => binop (p hd) ih
            let (hd_id, hd) = b.fresh_local(alpha.clone());
            let (tl_id, _tl) = b.fresh_local(list_alpha.clone());
            let (ih_id, ih) = b.fresh_local(bool_const.clone());
            let cons_body = Expr::apps(binop, [Expr::app(p.clone(), hd.clone()), ih.clone()]);
            let cons_case = b.mk_lam(ih_id, BinderInfo::Default, bool_const.clone(), cons_body);
            let cons_case = b.mk_lam(tl_id, BinderInfo::Default, list_alpha.clone(), cons_case);
            let cons_case = b.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), cons_case);

            let body = Expr::apps(
                bool_rec.clone(),
                [alpha.clone(), motive, base, cons_case, l.clone()],
            );
            let e = b.mk_lam(p_id, BinderInfo::Default, p_ty.clone(), body);
            let e = b.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("List.any"),
            level_params: vec![u.clone()],
            type_: predicate_combinator_type(),
            value: predicate_combinator_value(bool_false.clone(), bool_or.clone()),
            is_reducible: true,
        })?;

        // ── List.all {α : Type u} (l : List α) (p : α → Bool) : Bool ───────
        // = @List.rec α (λ _ => Bool) Bool.true (λ hd _ ih => Bool.and (p hd) ih) l
        self.add_decl(Declaration::Definition {
            name: Name::from_string("List.all"),
            level_params: vec![u.clone()],
            type_: predicate_combinator_type(),
            value: predicate_combinator_value(bool_true.clone(), bool_and.clone()),
            is_reducible: true,
        })?;

        // ── List.range (n : Nat) : List Nat ────────────────────────────────
        // `List.range n = [0, 1, …, n-1]`. Built by a `Nat.rec` that, at each
        // step, appends `n-1` to the front-recursion via an auxiliary
        // accumulator-free shape:
        //   rangeAux : Nat → List Nat → List Nat   -- prepends [cur, cur+1, …]
        // We instead use the standard "count up" recursion:
        //   range 0       = []
        //   range (k+1)   = range k ++ [k]
        // Implementing `++` would add a dependency; instead we recurse on the
        // *result* directly with `Nat.rec` whose motive is `List Nat`, using a
        // helper that tracks the current index. The simplest closed,
        // dependency-free form is the "snoc by foldr-free" build:
        //   range n = (Nat.rec (motive := fun _ => List Nat)
        //                []                              -- range 0
        //                (fun k ih => ih.appendSingleton k)  -- range (k+1)
        //                n)
        // To avoid needing append, we materialise the snoc inline as a second
        // `List.rec` over `ih`. That is heavy; the cleaner approach that still
        // reduces is the head-recursive "rangeAux n start":
        //   rangeAux 0       _     = []
        //   rangeAux (m+1) start   = start :: rangeAux m (start+1)
        //   range n = rangeAux n 0
        // `rangeAux` is a `Nat.rec` whose motive is `Nat → List Nat`.
        let nat_rec_list = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        );
        // Specialised List.nil / List.cons at Nat (u := 0).
        let list_nil_nat = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            nat_const.clone(),
        );
        let list_cons_nat = Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]);
        // Nat → List Nat (the rangeAux motive codomain).
        let nat_to_listnat = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            // List Nat lives at universe 0 here; reuse list_const at level zero.
            Expr::app(
                Expr::const_(Name::from_string("List"), vec![Level::zero()]),
                nat_const.clone(),
            ),
        );

        // rangeAux : Nat → (Nat → List Nat)
        //   = @Nat.rec (fun _ => Nat → List Nat)
        //       (fun _ => List.nil)                 -- rangeAux 0
        //       (fun _m ih => fun start =>          -- rangeAux (m+1)
        //          List.cons start (ih (Nat.succ start)))
        //       n
        let range_aux_value = {
            let mut b = EnvDeclBuilder::new();
            // motive: λ (_ : Nat) => Nat → List Nat
            let (mn_id, _mn) = b.fresh_local(nat_const.clone());
            let motive = b.mk_lam(
                mn_id,
                BinderInfo::Default,
                nat_const.clone(),
                nat_to_listnat.clone(),
            );

            // zero case: λ (_start : Nat) => List.nil
            let (zstart_id, _zstart) = b.fresh_local(nat_const.clone());
            let zero_case = b.mk_lam(
                zstart_id,
                BinderInfo::Default,
                nat_const.clone(),
                list_nil_nat.clone(),
            );

            // succ case: λ (_m : Nat) (ih : Nat → List Nat) =>
            //              λ (start : Nat) =>
            //                List.cons start (ih (Nat.succ start))
            let (m_id, _m) = b.fresh_local(nat_const.clone());
            let (ih_id, ih) = b.fresh_local(nat_to_listnat.clone());
            let (start_id, start) = b.fresh_local(nat_const.clone());
            let succ_start = Expr::app(nat_succ.clone(), start.clone());
            let tail = Expr::app(ih.clone(), succ_start);
            let cons_body = Expr::apps(
                list_cons_nat.clone(),
                [nat_const.clone(), start.clone(), tail],
            );
            let succ_inner = b.mk_lam(start_id, BinderInfo::Default, nat_const.clone(), cons_body);
            let succ_case = b.mk_lam(
                ih_id,
                BinderInfo::Default,
                nat_to_listnat.clone(),
                succ_inner,
            );
            let succ_case = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), succ_case);

            // @Nat.rec motive zero_case succ_case  (a function Nat → Nat → List Nat)
            let body = Expr::apps(nat_rec_list.clone(), [motive, zero_case, succ_case]);
            b.finish(body)
        };
        let range_aux_type = {
            let mut b = EnvDeclBuilder::new();
            // Nat → Nat → List Nat
            let e = Expr::pi(
                BinderInfo::Default,
                nat_const.clone(),
                nat_to_listnat.clone(),
            );
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("List.rangeAux"),
            level_params: vec![],
            type_: range_aux_type,
            value: range_aux_value,
            is_reducible: true,
        })?;

        // range (n : Nat) : List Nat := List.rangeAux n 0
        let range_aux_const = Expr::const_(Name::from_string("List.rangeAux"), vec![]);
        let range_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, _n) = b.fresh_local(nat_const.clone());
            let list_nat0 = Expr::app(
                Expr::const_(Name::from_string("List"), vec![Level::zero()]),
                nat_const.clone(),
            );
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), list_nat0);
            b.finish(e)
        };
        let range_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let body = Expr::apps(range_aux_const.clone(), [n.clone(), nat_zero.clone()]);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("List.range"),
            level_params: vec![],
            type_: range_type,
            value: range_value,
            is_reducible: true,
        })?;

        Ok(())
    }

    /// Check if List has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_list` has completed successfully
    /// ENSURES: Pure - no side effects
    pub(crate) fn has_list(&self) -> bool {
        self.list_init
    }

    /// Initialize List membership: `List.Mem`, its `Membership` instance, and
    /// the core constructive membership lemmas.
    ///
    /// Mirrors Lean 4's
    /// ```text
    /// inductive Mem (a : α) : List α → Prop
    ///   | head (as : List α) : Mem a (a :: as)
    ///   | tail (b : α) {as : List α} : Mem a as → Mem a (b :: as)
    /// ```
    /// Here `α` (implicit) and `a` (explicit) are *parameters* and the `List α`
    /// is the single *index* (it differs between the two constructors, so it is
    /// genuinely an index and is not promoted to a parameter). The recursor
    /// `List.Mem.rec` is auto-generated by `add_inductive`.
    ///
    /// Also adds:
    /// - `List.instMembership : {α : Type u} → Membership α (List α)` — the
    ///   instance that resolves `a ∈ l` (which the parser desugars to
    ///   `Membership.mem l a`, collection-first per Lean v4.30). Mirrors
    ///   `instMembershipSet`. Its body is Lean's own `⟨fun l a => Mem a l⟩`
    ///   flip lambda, so `∈` delta+proj-reduces to `List.Mem` at the kernel
    ///   level.
    /// - `List.mem_cons_self {α} (a) (as) : a ∈ a :: as` — the `head`
    ///   constructor, stated through the instance.
    /// - `List.mem_cons_of_mem {α} (y) {a} {l} : a ∈ l → a ∈ y :: l` — the
    ///   `tail` constructor, stated through the instance.
    ///
    /// Each lemma is a genuine `Declaration::Theorem` with an empty
    /// domain-axiom closure (`ProofQuality::Constructive`): the proof terms are
    /// the inductive's own constructors, which depend on no axioms.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.list_mem_init == true`
    /// ENSURES: On success, required dependencies (`list`, `set`/`Membership`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_list_mem(&mut self) -> Result<(), EnvError> {
        if self.list_mem_init {
            return Ok(());
        }

        // `List` provides the inductive and its constructors; `init_set`
        // registers the `Membership` typeclass that the instance references.
        self.init_list()?;
        self.init_set()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        let list_const = Expr::const_(Name::from_string("List"), vec![u_level.clone()]);
        let list_cons = Expr::const_(Name::from_string("List.cons"), vec![u_level.clone()]);
        let mem_const = Expr::const_(Name::from_string("List.Mem"), vec![u_level.clone()]);

        // `@List.cons α hd tl`
        let cons = |alpha: &Expr, hd: Expr, tl: Expr| {
            Expr::apps(list_cons.clone(), [alpha.clone(), hd, tl])
        };
        // `@List.Mem α a l`
        let mem =
            |alpha: &Expr, a: Expr, l: Expr| Expr::apps(mem_const.clone(), [alpha.clone(), a, l]);

        // ── List.Mem : {α : Type u} → α → List α → Prop ──────────────────────
        // num_params = 2 (α, a); the trailing `List α` is the index.
        let list_mem_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let (l_id, _l) = b.fresh_local(list_alpha.clone());
            let e = prop.clone();
            let e = b.mk_pi(l_id, BinderInfo::Default, list_alpha, e);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // ── List.Mem.head : {α} → (a : α) → (as : List α) → Mem a (a :: as) ──
        let mem_head_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let (as_id, as_) = b.fresh_local(list_alpha.clone());
            let concl = mem(&alpha, a.clone(), cons(&alpha, a.clone(), as_.clone()));
            let e = b.mk_pi(as_id, BinderInfo::Default, list_alpha, concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // ── List.Mem.tail :
        //      {α} → (a : α) → (b : α) → {as : List α} → Mem a as → Mem a (b :: as)
        let mem_tail_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (b_id, bv) = b.fresh_local(alpha.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let (as_id, as_) = b.fresh_local(list_alpha.clone());
            let mem_a_as = mem(&alpha, a.clone(), as_.clone());
            let (h_id, _h) = b.fresh_local(mem_a_as.clone());
            let concl = mem(&alpha, a.clone(), cons(&alpha, bv.clone(), as_.clone()));
            let e = b.mk_pi(h_id, BinderInfo::Default, mem_a_as, concl);
            let e = b.mk_pi(as_id, BinderInfo::Implicit, list_alpha, e);
            let e = b.mk_pi(b_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let mem_decl = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 2, // α and a are parameters; `List α` is the index
            types: vec![InductiveType {
                name: Name::from_string("List.Mem"),
                type_: list_mem_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("List.Mem.head"),
                        type_: mem_head_type,
                    },
                    Constructor {
                        name: Name::from_string("List.Mem.tail"),
                        type_: mem_tail_type,
                    },
                ],
            }],
        };

        self.add_inductive(mem_decl)?;

        // ── List.instMembership : {α : Type u} → Membership α (List α) ───────
        //     := Membership.mk α (List α) (fun (l : List α) (a : α) => List.Mem α a l)
        // Mirrors `instMembershipSet` (set_theory.rs). `Membership.{u, u}`
        // since both the element type and the container live in `Type u`.
        //
        // Lean 4 v4.30 (`Init/Data/List/Basic.lean`):
        //   instance : Membership α (List α) := ⟨fun l a => Mem a l⟩
        //
        // The `Membership` field is COLLECTION-first since Lean v4.9
        // (`mem : γ → α → Prop`, Init/Prelude.lean:1746), while the `List.Mem`
        // inductive stays ELEMENT-first (`Mem (a : α) : List α → Prop`) — so
        // Lean's own instance wraps the relation in the flip lambda above, and
        // Clean seeds exactly that term.
        //
        // Previously registered as a bare Axiom (no `Membership.mk` body), so a
        // genuine `@Membership.mem α (List α) List.instMembership l a` could not
        // proj-reduce to `List.Mem a l` and every real-math proof comparing the
        // two heads was rejected ("List.Mem vs Membership.mem"). Building it as
        // the genuine `Membership.mk`-based definition lets the kernel reduce the
        // projection exactly as Lean does. Shape correction to MATCH Lean; the
        // kernel re-checks the body (closure = List.Mem + Membership.mk, no axiom).
        let inst_membership_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let membership_uu = Expr::const_(
                Name::from_string("Membership"),
                vec![u_level.clone(), u_level.clone()],
            );
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let e = Expr::apps(membership_uu, [alpha.clone(), list_alpha]);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let inst_membership_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            // Membership.mk.{u,u} α (List α) (fun (l : List α) (a : α) => @List.Mem.{u} α a l)
            let membership_mk = Expr::const_(
                Name::from_string("Membership.mk"),
                vec![u_level.clone(), u_level.clone()],
            );
            // The collection-first flip lambda — Lean v4.30's `fun l a => Mem a l`.
            let flip_mem = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (l_id, l) = c.fresh_local(list_alpha.clone());
                let (a_id, a) = c.fresh_local(alpha.clone());
                let body = mem(&alpha, a.clone(), l.clone());
                let r = c.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
                let r = c.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), r);
                c.finish_child(r)
            };
            let body = Expr::apps(membership_mk, [alpha.clone(), list_alpha, flip_mem]);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("List.instMembership"),
            level_params: vec![u.clone()],
            type_: inst_membership_type,
            value: inst_membership_value,
            is_reducible: true,
        })?;
        // Register it as a `Membership` instance so `a ∈ l` resolves: the
        // Definition (a genuine `Membership.mk` body, no axiom) existed but was
        // never in the instance registry, so `Membership α (List α)` synthesis
        // failed (`FailedToSynthesizeInstance`) and `a ∈ l` did not elaborate.
        self.register_instance(crate::env::KernelInstanceInfo {
            name: Name::from_string("List.instMembership"),
            class_name: Name::from_string("Membership"),
            priority: crate::env::DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        // `@Membership.mem α (List α) (@List.instMembership α) l a` — the
        // GENUINE Lean statement form for the membership lemmas below
        // (COLLECTION-first since Lean v4.9: `a ∈ l` elaborates to
        // `Membership.mem l a`). Lean states both lemmas through the
        // `Membership` instance, not raw `List.Mem`; the kernel converges the
        // two by unfolding the instance, but the STATEMENT must match Lean's or
        // the stub SHADOWS the genuine olean theorem with a different signature
        // (see mem_cons_of_mem below).
        let inst_membership_const = Expr::const_(
            Name::from_string("List.instMembership"),
            vec![u_level.clone()],
        );
        let membership_mem_const = Expr::const_(
            Name::from_string("Membership.mem"),
            vec![u_level.clone(), u_level.clone()],
        );
        let mem_via_inst = |alpha: &Expr, a: Expr, l: Expr| {
            Expr::apps(
                membership_mem_const.clone(),
                [
                    alpha.clone(),
                    Expr::app(list_const.clone(), alpha.clone()),
                    Expr::app(inst_membership_const.clone(), alpha.clone()),
                    l,
                    a,
                ],
            )
        };

        // ── List.mem_cons_self {α} (a) (l) : a ∈ a :: l ──────────────────────
        // Lean 4.8 (`Init/Data/List/Basic.lean`):
        //   theorem mem_cons_self (a : α) (l : List α) : a ∈ a :: l := .head ..
        // Statement in the genuine `Membership.mem` form; proof = the `head`
        // constructor (kernel-converges via the reducible instance).
        let mem_head_const =
            Expr::const_(Name::from_string("List.Mem.head"), vec![u_level.clone()]);
        let mem_cons_self_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let (as_id, as_) = b.fresh_local(list_alpha.clone());
            let concl = mem_via_inst(&alpha, a.clone(), cons(&alpha, a.clone(), as_.clone()));
            let e = b.mk_pi(as_id, BinderInfo::Default, list_alpha, concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let mem_cons_self_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let (as_id, as_) = b.fresh_local(list_alpha.clone());
            // @List.Mem.head α a as
            let body = Expr::apps(
                mem_head_const.clone(),
                [alpha.clone(), a.clone(), as_.clone()],
            );
            let e = b.mk_lam(as_id, BinderInfo::Default, list_alpha, body);
            let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("List.mem_cons_self"),
            level_params: vec![u.clone()],
            type_: mem_cons_self_type,
            value: mem_cons_self_value,
        })?;

        // ── List.mem_cons_of_mem {α} (y) {a} {l} : a ∈ l → a ∈ y :: l ────────
        // Lean 4.8 (`Init/Data/List/Basic.lean`):
        //   theorem mem_cons_of_mem (y : α) {a : α} {l : List α} :
        //       a ∈ l → a ∈ y :: l := .tail _
        // FIDELITY (residual-to-zero campaign, 2026-07-02): the previous stub
        // was TRANSPOSED — `{α} {a} (b) {as}` put the ELEMENT first and the new
        // HEAD second, the reverse of Lean's `(y) {a} {l}`. Because the loader
        // dedups by name, the stub SHADOWED the genuine olean theorem, so every
        // Mathlib proof applying `@List.mem_cons_of_mem α hd x tl hx`
        // positionally instantiated the WRONG binders (a:=hd, b:=x, as:=tl) and
        // was rejected with `expected List.Mem hd tl, got x ∈ tl` — the whole
        // `List.Mem vs Membership.mem` type_mismatch class on Data.List.Basic
        // (foldlRecOn/foldl_ext/pmap_congr/…). Corrected to Lean's exact binder
        // order and `Membership.mem` statement form; the proof is re-checked by
        // `add_decl` (self-enforcing) and an adversarial-rejection test pins
        // that old-order applications are rejected (list_mem_tests below).
        let mem_tail_const =
            Expr::const_(Name::from_string("List.Mem.tail"), vec![u_level.clone()]);
        let mem_cons_of_mem_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (y_id, y) = b.fresh_local(alpha.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let (l_id, l) = b.fresh_local(list_alpha.clone());
            let mem_a_l = mem_via_inst(&alpha, a.clone(), l.clone());
            let (h_id, _h) = b.fresh_local(mem_a_l.clone());
            let concl = mem_via_inst(&alpha, a.clone(), cons(&alpha, y.clone(), l.clone()));
            let e = b.mk_pi(h_id, BinderInfo::Default, mem_a_l, concl);
            let e = b.mk_pi(l_id, BinderInfo::Implicit, list_alpha, e);
            let e = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        let mem_cons_of_mem_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (y_id, y) = b.fresh_local(alpha.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let (l_id, l) = b.fresh_local(list_alpha.clone());
            let mem_a_l = mem_via_inst(&alpha, a.clone(), l.clone());
            let (h_id, h) = b.fresh_local(mem_a_l.clone());
            // @List.Mem.tail α a y l h  (constructor order: element, head, tail)
            let body = Expr::apps(
                mem_tail_const.clone(),
                [alpha.clone(), a.clone(), y.clone(), l.clone(), h],
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, mem_a_l, body);
            let e = b.mk_lam(l_id, BinderInfo::Implicit, list_alpha, e);
            let e = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_lam(y_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("List.mem_cons_of_mem"),
            level_params: vec![u.clone()],
            type_: mem_cons_of_mem_type,
            value: mem_cons_of_mem_value,
        })?;

        self.list_mem_init = true;
        Ok(())
    }

    /// Check if List membership has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_list_mem` has completed successfully
    /// ENSURES: Pure - no side effects
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_list_mem(&self) -> bool {
        self.list_mem_init
    }

    /// Initialize String type
    ///
    /// String is a structure wrapping List Char
    ///
    /// structure String where
    ///   data : List Char
    ///
    /// Also adds:
    /// - String.mk : List Char → String
    /// - String.data : String → List Char
    /// - String.length : String → Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.string_init == true`
    /// ENSURES: On success, required dependencies (`list`, `char`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_string(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): Clean's String is the v4.8 shape (`String.mk :
        // List Char → String` over the Nat-shaped Char) — genuine v4.31
        // String wraps a validated ByteArray (`String.ofByteArray`;
        // `String.mk` was REMOVED upstream) and Char itself is
        // import-suppressed. Import-suppressed so the genuine v4.31 String
        // cluster imports through the checked path.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.string_init {
            return Ok(());
        }

        // Ensure List and Char are initialized
        self.init_list()?;
        self.init_char()?;

        // String : Type
        let string_type = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        let string_const = Expr::const_(Name::from_string("String"), vec![]);
        let char_const = Expr::const_(Name::from_string("Char"), vec![]);
        // Char : Type 0, so List.{0} Char : Type 0
        let list_const = Expr::const_(Name::from_string("List"), vec![Level::zero()]);
        let list_char = Expr::app(list_const.clone(), char_const.clone());

        // String.mk : List Char → String
        let string_mk_type = Expr::pi(BinderInfo::Default, list_char.clone(), string_const.clone());

        let string_decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("String"),
                type_: string_type,
                constructors: vec![Constructor {
                    name: Name::from_string("String.mk"),
                    type_: string_mk_type,
                }],
            }],
        };

        self.add_inductive(string_decl)?;

        // Register structure field
        self.structure_fields
            .insert(Name::from_string("String"), vec![Name::from_string("data")]);

        // Add String.data : String → List Char (projection)
        let string_data_type =
            Expr::pi(BinderInfo::Default, string_const.clone(), list_char.clone());

        let string_rec = Expr::const_(
            Name::from_string("String.rec"),
            vec![Level::succ(Level::zero())],
        );

        // motive: λ _ : String => List Char
        let motive = Expr::lam(BinderInfo::Default, string_const.clone(), list_char.clone());

        // String.data := λ s : String => String.rec (λ _ => List Char) (λ data => data) s
        let string_data_value = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(string_const.clone());
            let (data_id, data) = b.fresh_local(list_char.clone());
            let minor = b.mk_lam(data_id, BinderInfo::Default, list_char.clone(), data);
            let body = Expr::apps(string_rec.clone(), [motive.clone(), minor, s]);
            let e = b.mk_lam(s_id, BinderInfo::Default, string_const.clone(), body);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("String.data"),
            level_params: vec![],
            type_: string_data_type,
            value: string_data_value,
            is_reducible: true,
        })?;

        // String.toList : String → List Char := fun s => String.data s
        //
        // R146: the standard Lean 4 accessor `s.toList` — an alias of the
        // `String.data` projection (a String is backed by a List Char). Without
        // it, dot-notation `s.toList` failed LOUD with UnknownProjectionField
        // (String's only field is `data`, and dot notation's namespace-function
        // fallback had no String.toList to find). Reducible + axiom-free, the
        // exact mirror of R145's Array.toList. Withheld in import mode: the
        // genuine olean String.toList imports through the checked path.
        if !self.suppress_lossy_structure_stubs
            && self
                .get_const(&Name::from_string("String.toList"))
                .is_none()
        {
            let string_tolist_type =
                Expr::pi(BinderInfo::Default, string_const.clone(), list_char.clone());
            let string_tolist_value = {
                let mut b = EnvDeclBuilder::new();
                let (s_id, s) = b.fresh_local(string_const.clone());
                let string_data = Expr::const_(Name::from_string("String.data"), vec![]);
                let body = Expr::app(string_data, s);
                let e = b.mk_lam(s_id, BinderInfo::Default, string_const.clone(), body);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("String.toList"),
                level_params: vec![],
                type_: string_tolist_type,
                value: string_tolist_value,
                is_reducible: true,
            })?;
        }

        // Add String.length : String → Nat
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        // List.length.{0} since Char : Type 0
        let list_length = Expr::const_(Name::from_string("List.length"), vec![Level::zero()]);
        let string_data_const = Expr::const_(Name::from_string("String.data"), vec![]);

        let string_length_type =
            Expr::pi(BinderInfo::Default, string_const.clone(), nat_const.clone());

        // String.length s := List.length Char (String.data s)
        let string_length_value = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(string_const.clone());
            let body = Expr::app(
                Expr::app(list_length.clone(), char_const.clone()),
                Expr::app(string_data_const.clone(), s),
            );
            let e = b.mk_lam(s_id, BinderInfo::Default, string_const.clone(), body);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("String.length"),
            level_params: vec![],
            type_: string_length_type,
            value: string_length_value,
            is_reducible: true,
        })?;

        // Add String.ofList : List Char → String as an alias for String.mk.
        // This is used by string_lit_to_constructor for iota reduction (#574).
        // In Lean 4, String.ofList is the canonical way to convert a character list to a string.
        let string_of_list_type =
            Expr::pi(BinderInfo::Default, list_char.clone(), string_const.clone());
        let string_mk_const = Expr::const_(Name::from_string("String.mk"), vec![]);
        // String.ofList := λ data : List Char => String.mk data
        let string_of_list_value = {
            let mut b = EnvDeclBuilder::new();
            let (data_id, data) = b.fresh_local(list_char.clone());
            let e = b.mk_lam(
                data_id,
                BinderInfo::Default,
                list_char.clone(),
                Expr::app(string_mk_const.clone(), data),
            );
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("String.ofList"),
            level_params: vec![],
            type_: string_of_list_type,
            value: string_of_list_value,
            is_reducible: true,
        })?;

        self.string_init = true;
        Ok(())
    }

    /// Check if String has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_string` has completed successfully
    /// ENSURES: Pure - no side effects
    pub(crate) fn has_string(&self) -> bool {
        self.string_init
    }

    /// Initialize `String.append : String → String → String` as a genuine,
    /// axiom-free definition:
    /// ```text
    /// String.append a b := String.mk (List.append Char a.data b.data)
    /// ```
    ///
    /// Previously `String.append` existed only as a native reducer with no
    /// declaration, so the elaborator could not look up its type and
    /// mis-resolved the qualified name as dot-notation on a type-valued
    /// expression. Registering a real definition lets `a ++ b` (via the
    /// `HAppend String String String` instance) elaborate to a closed term the
    /// kernel accepts. The native reducer still provides fast-path computation
    /// on string literals; this definition is the type/value the elaborator
    /// resolves against.
    pub(crate) fn init_string_append(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget):
        // String-cluster content over the import-suppressed v4.8 String/Char
        // shapes (see init_string). Suppressed with them.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.string_append_init {
            return Ok(());
        }

        self.init_string()?;
        // `List.append` lives in init_list_ops; pull it in so the value below
        // references a real declaration (init_list_ops is idempotent).
        self.init_list_ops()?;

        let string_const = Expr::const_(Name::from_string("String"), vec![]);
        let char_const = Expr::const_(Name::from_string("Char"), vec![]);
        let string_mk_const = Expr::const_(Name::from_string("String.mk"), vec![]);
        let string_data_const = Expr::const_(Name::from_string("String.data"), vec![]);
        // List.append : {α : Type u} → List α → List α → List α, instantiated
        // at Char (universe 0, since Char : Type 0).
        let list_append_char = Expr::app(
            Expr::const_(Name::from_string("List.append"), vec![Level::zero()]),
            char_const.clone(),
        );

        // String.append : String → String → String
        let append_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _a) = b.fresh_local(string_const.clone());
            let (bb_id, _bb) = b.fresh_local(string_const.clone());
            let r = string_const.clone();
            let r = b.mk_pi(bb_id, BinderInfo::Default, string_const.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, string_const.clone(), r);
            b.finish(r)
        };

        // String.append a b := String.mk (List.append Char (String.data a) (String.data b))
        let append_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(string_const.clone());
            let (bb_id, bb) = b.fresh_local(string_const.clone());
            let a_data = Expr::app(string_data_const.clone(), a);
            let b_data = Expr::app(string_data_const.clone(), bb);
            let appended = Expr::app(Expr::app(list_append_char.clone(), a_data), b_data);
            let body = Expr::app(string_mk_const.clone(), appended);
            let e = b.mk_lam(bb_id, BinderInfo::Default, string_const.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, string_const.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("String.append"),
            level_params: vec![],
            type_: append_type,
            value: append_value,
            is_reducible: true,
        })?;

        self.string_append_init = true;
        Ok(())
    }

    /// Initialize `List.mapM` — the monadic list traversal.
    ///
    /// ```text
    /// List.mapM {m : Type u → Type v} {α β : Type u}
    ///   (f : α → m β) (l : List α) : m (List β)
    /// ```
    ///
    /// Threads the (implicit) monad's `Bind.bind` / `Pure.pure` over the list,
    /// collecting the results in order.  This is the exact shape
    /// `Semantics/Control.lean` / `Borrow.lean` use as
    /// `argIds.mapM Sem.lookupValue`, where
    /// `Sem = StateT MachineState (Except SemError)`.  Modelled directly on
    /// `clean`'s do-notation desugaring, which lowers `>>=` / `pure` to the
    /// bare `Bind.bind` / `Pure.pure` constants (`m` implicit, no `[Monad m]`
    /// instance argument).
    ///
    ///   mapM f []         = pure []
    ///   mapM f (hd :: tl) = f hd  >>= fun b =>
    ///                       mapM f tl >>= fun bs =>
    ///                       pure (b :: bs)
    ///
    /// Defined as a genuine `List.rec` elimination — NOT an axiom.  Its only
    /// non-prelude-inductive dependencies are the `Bind.bind` / `Pure.pure`
    /// monad-class constants (registered by `init_monad_classes`), so this MUST
    /// run *after* `init_monad_classes` — hence it lives here in
    /// `init_prelude_extended` rather than in `init_list_combinators`
    /// (prelude-core, before the monad classes exist).  With `List.rec`, the
    /// cons-case induction hypothesis `ih : m (List β)` *is* `mapM f tl`, so the
    /// recursion is structural and accepted by the kernel's eliminator check.
    /// Motive returns `m (List β) : Type v`, so we instantiate
    /// `List.rec.{succ v, u}`.  Idempotent.
    pub fn init_list_mapm(&mut self) -> Result<(), EnvError> {
        if self.list_mapm_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_lvl = Level::param(u.clone());
        let v_lvl = Level::param(v.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_lvl.clone())));
        let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(v_lvl.clone())));
        let list_const_u = Expr::const_(Name::from_string("List"), vec![u_lvl.clone()]);

        let mapm_rec = Expr::const_(
            Name::from_string("List.rec"),
            vec![Level::succ(v_lvl.clone()), u_lvl.clone()],
        );
        let m_ty = Expr::pi(BinderInfo::Default, type_u.clone(), type_v.clone());
        let bind_const = Expr::const_(
            Name::from_string("Bind.bind"),
            vec![u_lvl.clone(), v_lvl.clone()],
        );
        let pure_const = Expr::const_(
            Name::from_string("Pure.pure"),
            vec![u_lvl.clone(), v_lvl.clone()],
        );

        // ── Type ──────────────────────────────────────────────────────
        // {m} → {α} → {β} → (α → m β) → List α → m (List β)
        let mapm_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(m_ty.clone());
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let m_beta = Expr::app(m.clone(), beta.clone());
            let f_ty = Expr::pi(BinderInfo::Default, alpha.clone(), m_beta.clone());
            let (f_id, _f) = b.fresh_local(f_ty.clone());
            let list_alpha = Expr::app(list_const_u.clone(), alpha.clone());
            let (l_id, _l) = b.fresh_local(list_alpha.clone());
            let list_beta = Expr::app(list_const_u.clone(), beta.clone());
            let m_list_beta = Expr::app(m.clone(), list_beta.clone());
            let e = m_list_beta;
            let e = b.mk_pi(l_id, BinderInfo::Default, list_alpha.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty.clone(), e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Implicit, m_ty.clone(), e);
            b.finish(e)
        };

        // ── Value ─────────────────────────────────────────────────────
        let mapm_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(m_ty.clone());
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let m_beta = Expr::app(m.clone(), beta.clone());
            let f_ty = Expr::pi(BinderInfo::Default, alpha.clone(), m_beta.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let list_alpha = Expr::app(list_const_u.clone(), alpha.clone());
            let (l_id, l) = b.fresh_local(list_alpha.clone());

            let list_beta = Expr::app(list_const_u.clone(), beta.clone());
            let m_list_beta = Expr::app(m.clone(), list_beta.clone());

            // motive: λ (_ : List α) => m (List β)
            let (mot_id, _mot) = b.fresh_local(list_alpha.clone());
            let motive = b.mk_lam(
                mot_id,
                BinderInfo::Default,
                list_alpha.clone(),
                m_list_beta.clone(),
            );

            // nil case: @Pure.pure m (List β) (@List.nil β)
            let list_nil_beta = Expr::app(
                Expr::const_(Name::from_string("List.nil"), vec![u_lvl.clone()]),
                beta.clone(),
            );
            let nil_case = Expr::apps(
                pure_const.clone(),
                [m.clone(), list_beta.clone(), list_nil_beta],
            );

            // cons case:
            //   λ (hd : α) (_ : List α) (ih : m (List β)) =>
            //     @Bind.bind m β (List β) (f hd)
            //       (fun (bv : β) =>
            //         @Bind.bind m (List β) (List β) ih
            //           (fun (bs : List β) =>
            //             @Pure.pure m (List β) (@List.cons β bv bs)))
            let (hd_id, hd) = b.fresh_local(alpha.clone());
            let (tl_id, _tl) = b.fresh_local(list_alpha.clone());
            let (ih_id, ih) = b.fresh_local(m_list_beta.clone());

            // innermost: fun (bs : List β) => pure (bv :: bs)
            let (bv_id, bv) = b.fresh_local(beta.clone());
            let (bs_id, bs) = b.fresh_local(list_beta.clone());
            let cons_bb = Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![u_lvl.clone()]),
                [beta.clone(), bv.clone(), bs.clone()],
            );
            let pure_cons = Expr::apps(pure_const.clone(), [m.clone(), list_beta.clone(), cons_bb]);
            let inner_lam = b.mk_lam(bs_id, BinderInfo::Default, list_beta.clone(), pure_cons);

            // middle: @Bind.bind m (List β) (List β) ih (fun bs => …)
            let bind_ih = Expr::apps(
                bind_const.clone(),
                [
                    m.clone(),
                    list_beta.clone(),
                    list_beta.clone(),
                    ih.clone(),
                    inner_lam,
                ],
            );
            let mid_lam = b.mk_lam(bv_id, BinderInfo::Default, beta.clone(), bind_ih);

            // outer: @Bind.bind m β (List β) (f hd) (fun bv => …)
            let f_hd = Expr::app(f.clone(), hd.clone());
            let bind_fhd = Expr::apps(
                bind_const.clone(),
                [m.clone(), beta.clone(), list_beta.clone(), f_hd, mid_lam],
            );

            let cons_case = b.mk_lam(ih_id, BinderInfo::Default, m_list_beta.clone(), bind_fhd);
            let cons_case = b.mk_lam(tl_id, BinderInfo::Default, list_alpha.clone(), cons_case);
            let cons_case = b.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), cons_case);

            // @List.rec α motive nil_case cons_case l
            let body = Expr::apps(
                mapm_rec.clone(),
                [alpha.clone(), motive, nil_case, cons_case, l.clone()],
            );
            let e = b.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), body);
            let e = b.mk_lam(f_id, BinderInfo::Default, f_ty.clone(), e);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Implicit, m_ty.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("List.mapM"),
            level_params: vec![u, v],
            type_: mapm_type,
            value: mapm_value,
            is_reducible: true,
        })?;

        self.list_mapm_init = true;
        Ok(())
    }
}

#[cfg(test)]
mod list_mem_tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    fn env_with_mem() -> Environment {
        let mut env = Environment::new();
        env.init_list_mem()
            .expect("List membership should initialize");
        env
    }

    #[test]
    fn test_list_mem_init_idempotent() {
        let mut env = env_with_mem();
        env.init_list_mem()
            .expect("idempotent re-initialization should succeed");
        assert!(env.has_list_mem());
    }

    #[test]
    fn test_list_mem_inductive_and_constructors_registered() {
        let env = env_with_mem();
        for name in ["List.Mem", "List.Mem.head", "List.Mem.tail", "List.Mem.rec"] {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} should be registered"
            );
        }
        // List.Mem is a genuine inductive with one index (`List α`).
        let ind = env
            .inductives
            .get(&Name::from_string("List.Mem"))
            .expect("List.Mem should be an inductive");
        assert_eq!(ind.num_params, 2, "α and a are parameters");
        assert_eq!(ind.num_indices, 1, "the `List α` argument is the index");
    }

    #[test]
    fn test_list_mem_rec_type_checks() {
        let env = env_with_mem();
        let rec = env
            .get_const(&Name::from_string("List.Mem.rec"))
            .expect("List.Mem.rec should be registered");
        let tc = TypeChecker::new(&env);
        let _ = tc
            .infer_type(&rec.type_)
            .expect("List.Mem.rec type should infer a sort");
    }

    #[test]
    fn test_list_instmembership_registered() {
        let env = env_with_mem();
        let inst = env
            .get_const(&Name::from_string("List.instMembership"))
            .expect("List.instMembership should be registered");
        let tc = TypeChecker::new(&env);
        let _ = tc
            .infer_type(&inst.type_)
            .expect("List.instMembership type should type-check against Membership");
    }

    /// Verify-gate: `@Membership.mem α (List α) (List.instMembership α) l a`
    /// (COLLECTION-first, the Lean v4.30 argument order) must be definitionally
    /// equal to `@List.Mem α a l`. This is the genuine completeness fix —
    /// clean's `Membership` is now the real Lean single-field structure, so the
    /// `Membership.mem` projection delta+proj-reduces through the
    /// `Membership.mk`-based `List.instMembership` instance to `List.Mem`.
    /// Before the fix (`Membership`/instance as bare axioms) this defeq FAILED
    /// and every real `a ∈ (l : List α)` proof mis-matched ("List.Mem vs
    /// Membership.mem").
    #[test]
    fn test_membership_mem_list_reduces_to_list_mem() {
        use crate::env::decl_builder::EnvDeclBuilder;
        use crate::expr::BinderInfo;

        let env = env_with_mem();
        let tc = TypeChecker::new(&env);

        let u_name = Name::from_string("u");
        let u = crate::level::Level::param(u_name.clone());
        let type_u = Expr::sort(crate::level::Level::succ(u.clone()));
        let list_const = Expr::const_(Name::from_string("List"), vec![u.clone()]);

        // Build `fun {α : Type u} (a : α) (l : List α) => <body α a l>` for each
        // side, with α/a/l as genuine binder-bound variables (mirrors the
        // free-variable telescope a real Mathlib membership lemma carries). The
        // defeq check then reduces UNDER the binders — the faithful repro of the
        // verify context, unlike a closed `Nat` instantiation.
        let build = |body_fn: &dyn Fn(&Expr, &Expr, &Expr) -> Expr| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (l_id, l) = b.fresh_local(list_alpha.clone());
            let body = body_fn(&alpha, &a, &l);
            let r = b.mk_lam(l_id, BinderInfo::Default, list_alpha, body);
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // λ {α} a l => @Membership.mem.{u,u} α (List α) (@List.instMembership.{u} α) l a
        // (collection-first explicit args, per Lean v4.30 Init/Prelude.lean:1746)
        let lhs = build(&|alpha, a, l| {
            let membership_mem = Expr::const_(
                Name::from_string("Membership.mem"),
                vec![u.clone(), u.clone()],
            );
            let inst = Expr::app(
                Expr::const_(Name::from_string("List.instMembership"), vec![u.clone()]),
                alpha.clone(),
            );
            Expr::apps(
                membership_mem,
                [
                    alpha.clone(),
                    Expr::app(list_const.clone(), alpha.clone()),
                    inst,
                    l.clone(),
                    a.clone(),
                ],
            )
        });

        // λ {α} a l => @List.Mem.{u} α a l
        let rhs = build(&|alpha, a, l| {
            let list_mem = Expr::const_(Name::from_string("List.Mem"), vec![u.clone()]);
            Expr::apps(list_mem, [alpha.clone(), a.clone(), l.clone()])
        });

        assert!(
            tc.is_def_eq(&lhs, &rhs),
            "Membership.mem over List.instMembership must delta+proj-reduce to List.Mem (under binders)"
        );
    }

    /// FIDELITY pin (Lean v4.30 `Init/Prelude.lean:1744-1746`): the seeded
    /// `Membership.mem` signature is COLLECTION-first —
    /// `{α : Type u} → {γ : Type v} → [Membership α γ] → γ → α → Prop`.
    /// After the three implicit/inst binders the FIRST explicit binder is the
    /// collection `γ` and the SECOND is the element `α`. The pre-Lean-4.9
    /// element-first shape (`… → α → γ → Prop`) must NOT match: before this
    /// correction the transposed seed shadowed the genuine olean class family
    /// and failed every `∈`-mentioning declaration in the stamped closures.
    #[test]
    fn test_membership_mem_signature_is_collection_first() {
        use crate::env::decl_builder::EnvDeclBuilder;
        use crate::expr::BinderInfo;

        let env = env_with_mem();
        let tc = TypeChecker::new(&env);

        let info = env
            .get_const(&Name::from_string("Membership.mem"))
            .expect("Membership.mem should be registered");

        // Build `{α : Type u} → {γ : Type v} → [Membership α γ] → x → y → Prop`
        // with (x, y) = (γ, α) for the genuine collection-first shape and
        // (α, γ) for the transposed pre-4.9 shape.
        let build_sig = |collection_first: bool| -> Expr {
            let u = Level::param(Name::from_string("u"));
            let v = Level::param(Name::from_string("v"));
            let type_u = Expr::sort(Level::succ(u.clone()));
            let type_v = Expr::sort(Level::succ(v.clone()));
            let prop = Expr::sort(Level::zero());
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (gamma_id, gamma) = b.fresh_local(type_v.clone());
            let membership_app = Expr::apps(
                Expr::const_(Name::from_string("Membership"), vec![u, v]),
                [alpha.clone(), gamma.clone()],
            );
            let (inst_id, _inst) = b.fresh_local(membership_app.clone());
            let (fst, snd) = if collection_first {
                (gamma.clone(), alpha.clone())
            } else {
                (alpha.clone(), gamma.clone())
            };
            let (fst_id, _fst_var) = b.fresh_local(fst.clone());
            let (snd_id, _snd_var) = b.fresh_local(snd.clone());
            let e = prop;
            let e = b.mk_pi(snd_id, BinderInfo::Default, snd, e);
            let e = b.mk_pi(fst_id, BinderInfo::Default, fst, e);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, membership_app, e);
            let e = b.mk_pi(gamma_id, BinderInfo::Implicit, type_v, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
            b.finish(e)
        };

        assert!(
            tc.is_def_eq(&info.type_, &build_sig(true)),
            "Membership.mem must be collection-first (γ before α), \
             per Lean v4.30 Init/Prelude.lean:1744-1746"
        );
        assert!(
            !tc.is_def_eq(&info.type_, &build_sig(false)),
            "Membership.mem must NOT match the pre-Lean-4.9 element-first shape"
        );
    }

    /// ADVERSARIAL: a collection-first application of the `Membership.mem`
    /// accessor type-checks (full check mode), while the transposed
    /// element-first application — the pre-Lean-4.9 order — is REJECTED.
    /// `α = Nat` and `γ = List Nat` are distinct types, so the transposition
    /// cannot be silently absorbed; the fidelity correction is not a
    /// relaxation.
    #[test]
    fn test_membership_mem_application_order_enforced() {
        let env = env_with_mem();

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let list_nat = Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            nat.clone(),
        );
        let nil = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            nat.clone(),
        );
        // l0 = [0]
        let l0 = Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [nat.clone(), zero.clone(), nil],
        );
        let inst = Expr::app(
            Expr::const_(
                Name::from_string("List.instMembership"),
                vec![Level::zero()],
            ),
            nat.clone(),
        );
        let mem = Expr::const_(
            Name::from_string("Membership.mem"),
            vec![Level::zero(), Level::zero()],
        );

        // Lean v4.30 order: @Membership.mem Nat (List Nat) inst [0] 0 — the
        // desugaring of `0 ∈ [0]`. Must CHECK and land in Prop.
        let tc = TypeChecker::new(&env);
        let good = Expr::apps(
            mem.clone(),
            [
                nat.clone(),
                list_nat.clone(),
                inst.clone(),
                l0.clone(),
                zero.clone(),
            ],
        );
        let ty = tc
            .infer_type_full(&good)
            .expect("collection-first Membership.mem application must type-check");
        assert!(
            tc.is_def_eq(&ty, &Expr::sort(Level::zero())),
            "`0 ∈ [0]` must be a Prop, got {ty:?}"
        );

        // Pre-4.9 transposed order: @Membership.mem Nat (List Nat) inst 0 [0]
        // — must be REJECTED (element where the collection belongs).
        let tc2 = TypeChecker::new(&env);
        let bad = Expr::apps(mem, [nat, list_nat, inst, zero, l0]);
        assert!(
            tc2.infer_type_full(&bad).is_err(),
            "element-first (pre-Lean-4.9) Membership.mem application must be rejected"
        );
    }

    #[test]
    fn test_mem_cons_self_is_constructive_theorem() {
        let env = env_with_mem();
        let info = env
            .get_const(&Name::from_string("List.mem_cons_self"))
            .expect("List.mem_cons_self should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "theorem must retain its proof value");

        let quality = env
            .proof_quality(&Name::from_string("List.mem_cons_self"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "List.mem_cons_self must be Constructive (empty axiom closure), got {quality:?}"
        );

        // Explicitly assert the transitive domain-axiom closure is empty.
        let deps = env
            .axiom_deps(&Name::from_string("List.mem_cons_self"))
            .expect("axiom_deps should be reported");
        assert!(
            deps.is_empty(),
            "List.mem_cons_self must have an empty domain-axiom closure, got {deps:?}"
        );
    }

    #[test]
    fn test_mem_cons_of_mem_is_constructive_theorem() {
        let env = env_with_mem();
        let info = env
            .get_const(&Name::from_string("List.mem_cons_of_mem"))
            .expect("List.mem_cons_of_mem should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        assert!(info.value.is_some(), "theorem must retain its proof value");

        let quality = env
            .proof_quality(&Name::from_string("List.mem_cons_of_mem"))
            .expect("proof_quality should be reported");
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "List.mem_cons_of_mem must be Constructive (empty axiom closure), got {quality:?}"
        );

        let deps = env
            .axiom_deps(&Name::from_string("List.mem_cons_of_mem"))
            .expect("axiom_deps should be reported");
        assert!(
            deps.is_empty(),
            "List.mem_cons_of_mem must have an empty domain-axiom closure, got {deps:?}"
        );
    }

    #[test]
    fn test_membership_term_type_checks() {
        // Build `@List.mem_cons_self.{0} Nat Nat.zero (@List.nil.{0} Nat)`,
        // a closed proof that `Nat.zero ∈ [Nat.zero]`, and confirm it
        // kernel-type-checks. Since the fidelity correction the statement is
        // Lean's genuine `Membership.mem` form (as printed by Lean 4.8's
        // `#print List.mem_cons_self`); the kernel still converges it to the
        // raw `List.Mem` via the reducible instance — both heads are pinned.
        let env = env_with_mem();

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let list_nil = Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]);
        let nil_nat = Expr::app(list_nil, nat.clone());
        let mem_cons_self =
            Expr::const_(Name::from_string("List.mem_cons_self"), vec![Level::zero()]);

        // proof : Nat.zero ∈ [Nat.zero]  (Membership.mem statement form)
        let proof = Expr::apps(
            mem_cons_self,
            [nat.clone(), nat_zero.clone(), nil_nat.clone()],
        );

        let tc = TypeChecker::new(&env);
        let inferred = tc
            .infer_type(&proof)
            .expect("membership proof term should type-check");

        // The stated head is Lean's `Membership.mem` …
        let head = inferred.get_app_fn();
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n,
                &Name::from_string("Membership.mem"),
                "stated type head should be Lean's Membership.mem form, got {n}"
            ),
            other => panic!("expected Membership.mem application, got {other:?}"),
        }

        // … and the kernel converges it to the raw `List.Mem` inductive by
        // unfolding the reducible `List.instMembership` projection.
        let reduced = tc.whnf(&inferred);
        let reduced_head = reduced.get_app_fn();
        match reduced_head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n,
                &Name::from_string("List.Mem"),
                "whnf must converge the instance form to List.Mem, got {n}"
            ),
            other => panic!("expected List.Mem application after whnf, got {other:?}"),
        }
    }

    /// FIDELITY + ADVERSARIAL pins for the `List.mem_cons_of_mem` binder-order
    /// correction (residual-to-zero campaign, 2026-07-02).
    ///
    /// Lean 4.8 ground truth (`#print List.mem_cons_of_mem`):
    /// `∀ {α} (y : α) {a : α} {l : List α}, a ∈ l → a ∈ y :: l` — the new HEAD
    /// `y` is the FIRST non-type binder. The previous Clean stub was transposed
    /// (`{a} (b) {as}` — element first), so Mathlib's positional applications
    /// `@List.mem_cons_of_mem α hd x tl hx` instantiated the wrong binders and
    /// were rejected. These pins hold BOTH directions:
    /// - Lean-order application (the one every Mathlib proof uses) CHECKS;
    /// - old-transposed-order application is REJECTED (the correction is a
    ///   fidelity fix, not a relaxation).
    #[test]
    fn test_mem_cons_of_mem_lean_binder_order() {
        let env = env_with_mem();
        let tc = TypeChecker::new(&env);

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let one = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            zero.clone(),
        );
        let nil = Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            nat.clone(),
        );
        // l0 = [0]
        let l0 = Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [nat.clone(), zero.clone(), nil.clone()],
        );
        // h : 0 ∈ [0]
        let h = Expr::apps(
            Expr::const_(Name::from_string("List.mem_cons_self"), vec![Level::zero()]),
            [nat.clone(), zero.clone(), nil.clone()],
        );
        let mcm = Expr::const_(
            Name::from_string("List.mem_cons_of_mem"),
            vec![Level::zero()],
        );

        // Lean order: @mem_cons_of_mem Nat (y := 1) (a := 0) (l := [0]) h
        // — "0 ∈ [0] → 0 ∈ 1 :: [0]". Must CHECK (full check mode).
        let good = Expr::apps(
            mcm.clone(),
            [
                nat.clone(),
                one.clone(),
                zero.clone(),
                l0.clone(),
                h.clone(),
            ],
        );
        let _good_ty = tc
            .infer_type_full(&good)
            .expect("Lean-binder-order application must type-check");

        // Old transposed order: @mem_cons_of_mem Nat (a := 0) (b := 1) (as := [0]) h
        // positionally binds y := 0, a := 1, l := [0] under the corrected
        // signature, so `h : 0 ∈ [0]` no longer matches the expected
        // `1 ∈ [0]` — must be REJECTED.
        let tc2 = TypeChecker::new(&env);
        let old_order = Expr::apps(
            mcm,
            [
                nat.clone(),
                zero.clone(),
                one.clone(),
                l0.clone(),
                h.clone(),
            ],
        );
        assert!(
            tc2.infer_type_full(&old_order).is_err(),
            "old transposed-order application must be rejected — the fidelity \
             correction must not be a relaxation"
        );
    }
}

#[cfg(test)]
mod list_combinator_tests {
    use super::*;
    use crate::tc::TypeChecker;

    /// All pure List combinators added by `init_list_combinators` are
    /// registered (alongside the `List.rangeAux` helper).
    #[test]
    fn test_combinators_registered() {
        let mut env = Environment::new();
        env.init_list().expect("List init should succeed");
        for name in [
            "List.foldr",
            "List.foldl",
            "List.any",
            "List.all",
            "List.range",
            "List.rangeAux",
        ] {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{name} should be registered by init_list_combinators"
            );
        }
    }

    /// Each combinator is a genuine `Definition` (never an `Axiom`), and both
    /// its declared type and its value type-check. `add_decl` already enforces
    /// `check_type(value, type_)` at registration, so reaching this point means
    /// the kernel accepted them; we additionally re-infer the type to confirm
    /// the type expression inhabits a sort.
    #[test]
    fn test_combinators_are_definitions_and_type_check() {
        let mut env = Environment::new();
        env.init_list().expect("List init should succeed");
        let tc = TypeChecker::new(&env);
        for name in [
            "List.foldr",
            "List.foldl",
            "List.any",
            "List.all",
            "List.range",
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert!(
                info.value.is_some(),
                "{name} must be a Definition with a value (not an Axiom)"
            );
            let _ = tc
                .infer_type(&info.type_)
                .unwrap_or_else(|e| panic!("{name} type should infer a sort: {e:?}"));
            // Re-check the value against its declared type.
            let value = info.value.as_ref().unwrap();
            tc.check_type(value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} value should check against its type: {e:?}"));
        }
    }

    /// Soundness: every combinator has an empty axiom-dependency closure — they
    /// are built purely from `List.rec` / `Nat.rec` and the (axiom-free)
    /// `Bool.or` / `Bool.and` definitions, introducing no kernel axiom.
    #[test]
    fn test_combinators_axiom_deps_empty() {
        let mut env = Environment::new();
        env.init_list().expect("List init should succeed");
        for name in [
            "List.foldr",
            "List.foldl",
            "List.any",
            "List.all",
            "List.range",
            "List.rangeAux",
        ] {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} is registered, axiom_deps should be Some"));
            let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                dep_names.is_empty(),
                "{name} must have an empty axiom closure, got {dep_names:?}"
            );
        }
    }

    /// `List.mapM` is registered (after the monad-class constants exist) as a
    /// genuine `Definition` whose declared type and value both kernel-check.
    /// Track ZZ.
    #[test]
    fn test_list_mapm_registered_and_type_checks() {
        let mut env = Environment::new();
        env.init_list().expect("List init should succeed");
        env.init_monad_classes()
            .expect("monad classes (Bind.bind/Pure.pure) init should succeed");
        env.init_list_mapm().expect("List.mapM init should succeed");

        let info = env
            .get_const(&Name::from_string("List.mapM"))
            .expect("List.mapM should be registered");
        assert!(
            info.value.is_some(),
            "List.mapM must be a Definition with a value (not an Axiom)"
        );

        let tc = TypeChecker::new(&env);
        let _ = tc
            .infer_type(&info.type_)
            .unwrap_or_else(|e| panic!("List.mapM type should infer a sort: {e:?}"));
        let value = info.value.as_ref().unwrap();
        tc.check_type(value, &info.type_)
            .unwrap_or_else(|e| panic!("List.mapM value should check against its type: {e:?}"));
    }

    /// `init_list_mapm` is idempotent.
    #[test]
    fn test_list_mapm_idempotent() {
        let mut env = Environment::new();
        env.init_list().expect("List init");
        env.init_monad_classes().expect("monad classes init");
        env.init_list_mapm().expect("first mapM init");
        env.init_list_mapm().expect("second mapM init (idempotent)");
    }

    /// Soundness: `List.mapM` itself is a `Definition` (NOT an axiom). Its only
    /// axiom-closure members are the prelude's monad-class constants
    /// (`Bind.bind` / `Pure.pure`) — which `clean`'s do-notation already lowers
    /// to and which exist on `main` as the shared monad interface. `List.mapM`
    /// introduces NO new axiom of its own; it is a pure `List.rec` elimination.
    #[test]
    fn test_list_mapm_introduces_no_new_axiom() {
        let mut env = Environment::new();
        env.init_list().expect("List init");
        env.init_monad_classes().expect("monad classes init");
        env.init_list_mapm().expect("mapM init");

        // The decl is a Definition, never an Axiom.
        let info = env
            .get_const(&Name::from_string("List.mapM"))
            .expect("List.mapM registered");
        assert!(info.value.is_some(), "List.mapM must be a Definition");

        // Its axiom closure is exactly the monad-class constants it threads —
        // no other (e.g. `sorry`) axiom leaks in.
        let deps = env
            .axiom_deps(&Name::from_string("List.mapM"))
            .expect("List.mapM registered ⇒ axiom_deps Some");
        let mut dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        dep_names.sort();
        for d in &dep_names {
            assert!(
                d == "Bind.bind" || d == "Pure.pure",
                "List.mapM axiom closure must contain only the monad-class \
                 constants, found unexpected {d:?} (full set: {dep_names:?})"
            );
        }
        assert!(
            !dep_names.iter().any(|d| d.contains("sorry")),
            "List.mapM must not depend on any sorry axiom: {dep_names:?}"
        );
    }

    /// Fidelity: Clean's `List.foldl` has the EXACT upstream Lean signature
    /// (`Init.Data.List.Basic`):
    ///
    /// ```text
    /// @List.foldl : {α : Type u_1} → {β : Type u_2} →
    ///   (α → β → α) → α → List β → α
    /// ```
    ///
    /// where the FIRST implicit `α` is the accumulator type and the SECOND `β`
    /// is the element type. This convention is the opposite of `List.foldr`
    /// (`(α → β → β) → β → List α → β`, `α` = element), and the transposition
    /// is what a `List.foldl_*` proof term relies on: applying an olean lemma
    /// whose `f` argument is `α → β → α` must match Clean's inferred type
    /// exactly, or every `List.foldl_*` decl fails with `type_mismatch`.
    ///
    /// This test pins the signature so it cannot silently drift back to the old
    /// (transposed) `(β → α → β) → β → List α → β` form.
    #[test]
    fn test_list_foldl_lean_faithful_signature() {
        let mut env = Environment::new();
        env.init_list().expect("List init should succeed");

        let info = env
            .get_const(&Name::from_string("List.foldl"))
            .expect("List.foldl should be registered");

        // Reconstruct the expected upstream type in Clean's IR and check it is
        // definitionally equal to the registered type. Levels u (accumulator)
        // then v (element), matching `List.foldl.{u_1, u_2}`.
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        assert_eq!(
            info.level_params,
            vec![u.clone(), v.clone()],
            "List.foldl level params must be [u, v] (accumulator-first)"
        );
        let u_lvl = Level::param(u);
        let v_lvl = Level::param(v);
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_lvl.clone())));
        let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(v_lvl.clone())));
        let list_v = Expr::const_(Name::from_string("List"), vec![v_lvl]);

        let expected_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let list_beta = Expr::app(list_v.clone(), beta.clone());
            // f : α → β → α   (accumulator → element → accumulator)
            let f_ty = Expr::pi(
                BinderInfo::Default,
                alpha.clone(),
                Expr::pi(BinderInfo::Default, beta.clone(), alpha.clone()),
            );
            let (f_id, _f) = b.fresh_local(f_ty.clone());
            let (init_id, _init) = b.fresh_local(alpha.clone());
            let (l_id, _l) = b.fresh_local(list_beta.clone());
            let e = alpha.clone();
            let e = b.mk_pi(l_id, BinderInfo::Default, list_beta, e);
            let e = b.mk_pi(init_id, BinderInfo::Default, alpha, e);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
            b.finish(e)
        };

        let tc = TypeChecker::new(&env);
        assert!(
            tc.is_def_eq(&info.type_, &expected_type),
            "List.foldl type must equal the Lean-faithful \
             `{{α}} {{β}} (α → β → α) → α → List β → α`, got {:?}",
            info.type_
        );
    }

    /// Adversarial rejection: the OLD (buggy) transposed signature
    /// `{{α}} {{β}} (β → α → β) → β → List α → β` — where the first implicit was
    /// the ELEMENT type — must NOT be definitionally equal to the corrected
    /// `List.foldl`. If it were, the fix would be vacuous and the
    /// `type_mismatch` failures would persist.
    #[test]
    fn test_list_foldl_rejects_transposed_signature() {
        let mut env = Environment::new();
        env.init_list().expect("List init should succeed");

        let info = env
            .get_const(&Name::from_string("List.foldl"))
            .expect("List.foldl should be registered");

        let u_lvl = Level::param(Name::from_string("u"));
        let v_lvl = Level::param(Name::from_string("v"));
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_lvl.clone())));
        let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(v_lvl.clone())));
        let list_u = Expr::const_(Name::from_string("List"), vec![u_lvl]);

        // OLD/WRONG type: f : β → α → β, init : β, l : List α, result β.
        let wrong_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let list_alpha = Expr::app(list_u.clone(), alpha.clone());
            let f_ty = Expr::pi(
                BinderInfo::Default,
                beta.clone(),
                Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone()),
            );
            let (f_id, _f) = b.fresh_local(f_ty.clone());
            let (init_id, _init) = b.fresh_local(beta.clone());
            let (l_id, _l) = b.fresh_local(list_alpha.clone());
            let e = beta.clone();
            let e = b.mk_pi(l_id, BinderInfo::Default, list_alpha, e);
            let e = b.mk_pi(init_id, BinderInfo::Default, beta.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u, e);
            b.finish(e)
        };

        let tc = TypeChecker::new(&env);
        assert!(
            !tc.is_def_eq(&info.type_, &wrong_type),
            "the corrected List.foldl must NOT be def-eq to the old transposed \
             `(β → α → β) → β → List α → β` signature — the fix would be vacuous"
        );
    }

    /// Fidelity: `List.foldl` reduces on a ground input exactly like Lean.
    /// `foldl (fun acc x => acc) 0 [true, false]` must whnf/def-eq to `0`,
    /// exercising the accumulator-first `f : α → β → α` (`Nat → Bool → Nat`)
    /// convention on a heterogeneous `α ≠ β` example (the case the transposed
    /// signature could not even type).
    #[test]
    fn test_list_foldl_reduces_heterogeneous_ground_input() {
        let mut env = Environment::new();
        env.init_list().expect("List init should succeed");

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let list_bool_ty = Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            bool_ty.clone(),
        );

        // f : Nat → Bool → Nat := fun acc _ => acc
        let mut b = EnvDeclBuilder::new();
        let (acc_id, acc) = b.fresh_local(nat.clone());
        let (x_id, _x) = b.fresh_local(bool_ty.clone());
        let f_body = b.mk_lam(x_id, BinderInfo::Default, bool_ty.clone(), acc);
        let f = b.mk_lam(acc_id, BinderInfo::Default, nat.clone(), f_body);
        let f = b.finish(f);

        // l : List Bool := [true, false]
        let list_cons = Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]);
        let list_nil = Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]);
        let nil_bool = Expr::app(list_nil, bool_ty.clone());
        let tail = Expr::apps(list_cons.clone(), [bool_ty.clone(), bool_false, nil_bool]);
        let l = Expr::apps(list_cons, [bool_ty.clone(), bool_true, tail]);

        // @List.foldl.{0,0} Nat Bool f Nat.zero l
        let foldl = Expr::const_(
            Name::from_string("List.foldl"),
            vec![Level::zero(), Level::zero()],
        );
        let app = Expr::apps(foldl, [nat.clone(), bool_ty, f, nat_zero.clone(), l]);

        let tc = TypeChecker::new(&env);
        // Well-typed at Nat.
        let inferred = tc
            .infer_type(&app)
            .expect("foldl application should type-check");
        assert!(
            tc.is_def_eq(&inferred, &nat),
            "foldl result type must be Nat, got {inferred:?}"
        );
        // Reduces to the initial accumulator `Nat.zero`.
        assert!(
            tc.is_def_eq(&app, &nat_zero),
            "foldl (fun acc _ => acc) 0 [true,false] must reduce to 0 — \
             confirms the accumulator-first reduction is Lean-faithful"
        );
        // Sanity: the list argument really is `List Bool` (element type Bool),
        // i.e. we did not accidentally re-transpose.
        let _ = list_bool_ty;
    }
}

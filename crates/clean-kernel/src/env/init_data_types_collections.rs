// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Always-on collection/structural data init entrypoints extracted from mixed
//! `data_types_collections.rs`.

use super::decl_builder::EnvDeclBuilder;
use super::init_shared::{type0_expr, InitLevelParam};
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Char type.
    pub fn init_char(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-04): Clean's Char is the v4.8 shape (val : Nat-backed pair
        // via Char.mk/ofNat) — genuine v4.31 Char is `⟨val : UInt32,
        // valid : val.isValidChar⟩` over the BitVec-based UInt32 carrier, so
        // the genuine order-instance proofs (`instLinearOrderChar._proof_*`,
        // `UInt8.toChar`) apply `UInt32.toBitVec (Char.val c)` and reject
        // against the Nat-shaped stub. Import-suppressed so the genuine v4.31
        // Char imports through the checked path (the UInt32 it needs is
        // already import-suppressed/imported — see init_uint8..64).
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.char_init {
            return Ok(());
        }

        self.init_nat()?;

        let char_const = Expr::const_(Name::from_string("Char"), vec![]);
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let char_mk_type = Expr::pi(BinderInfo::Default, nat_const.clone(), char_const.clone());

        let char_decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("Char"),
                type_: type0_expr(),
                constructors: vec![Constructor {
                    name: Name::from_string("Char.mk"),
                    type_: char_mk_type,
                }],
            }],
        };

        self.add_inductive(char_decl)?;
        self.structure_fields
            .insert(Name::from_string("Char"), vec![Name::from_string("val")]);

        let char_val_type = Expr::pi(BinderInfo::Default, char_const.clone(), nat_const.clone());
        let char_rec = Expr::const_(
            Name::from_string("Char.rec"),
            vec![Level::succ(Level::zero())],
        );
        let motive = Expr::lam(BinderInfo::Default, char_const.clone(), nat_const.clone());

        let char_val_value = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(char_const.clone());
            let (val_id, val) = b.fresh_local(nat_const.clone());
            let minor = b.mk_lam(val_id, BinderInfo::Default, nat_const.clone(), val);
            let body = Expr::apps(char_rec.clone(), [motive.clone(), minor, c]);
            let e = b.mk_lam(c_id, BinderInfo::Default, char_const.clone(), body);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Char.val"),
            level_params: vec![],
            type_: char_val_type,
            value: char_val_value,
            is_reducible: true,
        })?;

        let char_mk = Expr::const_(Name::from_string("Char.mk"), vec![]);
        let char_of_nat_type = Expr::pi(BinderInfo::Default, nat_const.clone(), char_const.clone());
        let char_of_nat_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat_const.clone());
            let e = b.mk_lam(
                n_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::app(char_mk.clone(), n),
            );
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Char.ofNat"),
            level_params: vec![],
            type_: char_of_nat_type,
            value: char_of_nat_value,
            is_reducible: true,
        })?;

        let char_val_const = Expr::const_(Name::from_string("Char.val"), vec![]);
        let char_to_nat_type = Expr::pi(BinderInfo::Default, char_const.clone(), nat_const.clone());
        let char_to_nat_value = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(char_const.clone());
            let e = b.mk_lam(
                c_id,
                BinderInfo::Default,
                char_const.clone(),
                Expr::app(char_val_const.clone(), c),
            );
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Char.toNat"),
            level_params: vec![],
            type_: char_to_nat_type,
            value: char_to_nat_value,
            is_reducible: true,
        })?;

        self.char_init = true;
        Ok(())
    }

    #[allow(dead_code)]
    pub(crate) fn has_char(&self) -> bool {
        self.char_init
    }

    /// Initialize List type (polymorphic linked list).
    pub fn init_list(&mut self) -> Result<(), EnvError> {
        if self.list_init {
            return Ok(());
        }

        self.init_nat()?;

        let u = InitLevelParam::new("u");
        let type_u = u.type_();
        let list_const = Expr::const_(Name::from_string("List"), vec![u.level.clone()]);
        let list_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());

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
            level_params: vec![u.name.clone()],
            num_params: 1,
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

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let list_rec = Expr::const_(
            Name::from_string("List.rec"),
            vec![Level::succ(u.level.clone()), u.level.clone()],
        );
        let list_nil = Expr::const_(Name::from_string("List.nil"), vec![u.level.clone()]);

        let list_tail_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
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

        let list_tail_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let (l_id, l) = b.fresh_local(list_alpha.clone());

            let (m_id, _m) = b.fresh_local(list_alpha.clone());
            let motive = b.mk_lam(
                m_id,
                BinderInfo::Default,
                list_alpha.clone(),
                list_alpha.clone(),
            );
            let nil_case = Expr::app(list_nil.clone(), alpha.clone());

            let (hd_id, _hd) = b.fresh_local(alpha.clone());
            let (tl_id, tl) = b.fresh_local(list_alpha.clone());
            let (ih_id, _ih) = b.fresh_local(list_alpha.clone());
            let cons_case = b.mk_lam(ih_id, BinderInfo::Default, list_alpha.clone(), tl.clone());
            let cons_case = b.mk_lam(tl_id, BinderInfo::Default, list_alpha.clone(), cons_case);
            let cons_case = b.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), cons_case);

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
            level_params: vec![u.name.clone()],
            type_: list_tail_type,
            value: list_tail_value,
            is_reducible: true,
        })?;

        let list_length_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let (l_id, _l) = b.fresh_local(list_alpha.clone());
            let e = b.mk_pi(l_id, BinderInfo::Default, list_alpha, nat_const.clone());
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let list_rec_nat = Expr::const_(
            Name::from_string("List.rec"),
            vec![Level::succ(Level::zero()), u.level.clone()],
        );
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

        let list_length_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let (l_id, l) = b.fresh_local(list_alpha.clone());

            let (m_id, _m) = b.fresh_local(list_alpha.clone());
            let motive = b.mk_lam(
                m_id,
                BinderInfo::Default,
                list_alpha.clone(),
                nat_const.clone(),
            );

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
            level_params: vec![u.name.clone()],
            type_: list_length_type,
            value: list_length_value,
            is_reducible: true,
        })?;

        self.list_init = true;
        Ok(())
    }

    #[allow(dead_code)]
    pub(crate) fn has_list(&self) -> bool {
        self.list_init
    }

    /// Initialize String type.
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

        self.init_list()?;
        self.init_char()?;

        let string_const = Expr::const_(Name::from_string("String"), vec![]);
        let char_const = Expr::const_(Name::from_string("Char"), vec![]);
        let list_const = Expr::const_(Name::from_string("List"), vec![Level::zero()]);
        let list_char = Expr::app(list_const.clone(), char_const.clone());
        let string_mk_type = Expr::pi(BinderInfo::Default, list_char.clone(), string_const.clone());

        let string_decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("String"),
                type_: type0_expr(),
                constructors: vec![Constructor {
                    name: Name::from_string("String.mk"),
                    type_: string_mk_type,
                }],
            }],
        };

        self.add_inductive(string_decl)?;
        self.structure_fields
            .insert(Name::from_string("String"), vec![Name::from_string("data")]);

        let string_data_type =
            Expr::pi(BinderInfo::Default, string_const.clone(), list_char.clone());
        let string_rec = Expr::const_(
            Name::from_string("String.rec"),
            vec![Level::succ(Level::zero())],
        );
        let motive = Expr::lam(BinderInfo::Default, string_const.clone(), list_char.clone());

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

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let list_length = Expr::const_(Name::from_string("List.length"), vec![Level::zero()]);
        let string_data_const = Expr::const_(Name::from_string("String.data"), vec![]);
        let string_length_type =
            Expr::pi(BinderInfo::Default, string_const.clone(), nat_const.clone());

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

        let string_of_list_type =
            Expr::pi(BinderInfo::Default, list_char.clone(), string_const.clone());
        let string_mk_const = Expr::const_(Name::from_string("String.mk"), vec![]);
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

    #[allow(dead_code)]
    pub(crate) fn has_string(&self) -> bool {
        self.string_init
    }
}

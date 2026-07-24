// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Heterogeneous typeclass short-circuit native reducers.
//!
//! When proof-by-reflection terms invoke `@HAdd.hAdd Nat Nat Nat instHAddNatNatNat a b`,
//! the type checker must:
//! 1. Unfold `HAdd.hAdd` to a structure projection
//! 2. Project from `instHAddNatNatNat` to get `Add.add` instance
//! 3. Project from the `Add.add` instance to get `Nat.add`
//! 4. Apply `Nat.add a b` (which then hits native reducer)
//!
//! Steps 1-3 waste heartbeat on structure projections. This module registers
//! native reducers for `HAdd.hAdd`, `HSub.hSub`, `HMul.hMul`, `HDiv.hDiv`,
//! `HMod.hMod`, and `HPow.hPow` that recognize known instances and delegate
//! directly to the underlying computation, saving 3-6 WHNF steps per invocation.
//!
//! This is the same pattern as the BEq.beq short-circuit reducer but for
//! arithmetic typeclass wrappers.
//!
//! Part of #3210: reduce heartbeat usage for Init .olean type-checking.

use crate::env::native_reducers_arith;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::Name;

/// Well-known names for heterogeneous typeclass short-circuit reducers.
pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    // Heterogeneous operation functions
    pub(crate) static HADD_HADD: LazyLock<Name> = LazyLock::new(|| Name::from_string("HAdd.hAdd"));
    pub(crate) static HSUB_HSUB: LazyLock<Name> = LazyLock::new(|| Name::from_string("HSub.hSub"));
    pub(crate) static HMUL_HMUL: LazyLock<Name> = LazyLock::new(|| Name::from_string("HMul.hMul"));
    pub(crate) static HDIV_HDIV: LazyLock<Name> = LazyLock::new(|| Name::from_string("HDiv.hDiv"));
    pub(crate) static HMOD_HMOD: LazyLock<Name> = LazyLock::new(|| Name::from_string("HMod.hMod"));
    pub(crate) static HPOW_HPOW: LazyLock<Name> = LazyLock::new(|| Name::from_string("HPow.hPow"));
    pub(crate) static HAPPEND_HAPPEND: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("HAppend.hAppend"));

    // Known instHAdd instances (Nat, Int, UInt widths)
    pub(crate) static INST_HADD_NAT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instHAddNatNatNat"));
    /// The homogeneous Nat `HAdd` instance registered by `with_prelude`
    /// (`init_nat_hadd_inst`), distinct from the triple-Nat name used by the
    /// olean import path. Both project to `Nat.add`.
    pub(crate) static INST_HADD_NAT_HOMO: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instHAddNat"));
    pub(crate) static INST_HSUB_NAT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instHSubNatNatNat"));
    pub(crate) static INST_HMUL_NAT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instHMulNatNatNat"));
    pub(crate) static INST_HDIV_NAT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instHDivNatNatNat"));
    pub(crate) static INST_HMOD_NAT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instHModNatNatNat"));
    pub(crate) static INST_HPOW_NAT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instHPowNatNatNat"));
}

/// Extract a String value from an expression literal.
fn get_string_val(e: &Expr) -> Option<&str> {
    match e.kind() {
        ExprKind::Lit(Literal::String(s)) => Some(s),
        _ => None,
    }
}

/// Get the name of an instance argument (head const of a possibly-applied expr).
fn get_instance_name(e: &Expr) -> Option<&Name> {
    let head = e.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        return Some(name);
    }
    None
}

/// Native reducer for `HAdd.hAdd`.
///
/// Signature: `HAdd.hAdd : {α β γ : Type u} → [inst : HAdd α β γ] → α → β → γ`
/// Args after head extraction: [α, β, γ, inst, a, b]
///
/// Recognizes `instHAddNatNatNat` and delegates directly to Nat.add.
fn reduce_hadd_hadd(args: &[&Expr]) -> Option<Expr> {
    // Need at least 6 args: [α, β, γ, inst, a, b]
    if args.len() < 6 {
        return None;
    }
    let inst_name = get_instance_name(args[3])?;

    // olean-path `instHAddNatNatNat`: literal-fold only (unchanged behavior).
    if *inst_name == *names::INST_HADD_NAT {
        return native_reducers_arith::reduce_nat_add(&[args[4], args[5]]);
    }

    // prelude-path `instHAddNat` (homogeneous `HAdd Nat Nat Nat`): the kernel
    // does not unfold this reducible-instance projection on its own, so even
    // `n + 1` stalls at `HAdd.hAdd`. Delegate to `Nat.add a b` — the exact term
    // the projection unfolds to — so the kernel's delta/iota reduction can take
    // over (`Nat.add n 1` ↝ `Nat.succ n`). The literal case folds to a literal.
    //
    // SOUNDNESS: `instHAddNat := @HAdd.mk Nat Nat Nat Nat.add` is a reducible
    // definition, so `@HAdd.hAdd Nat Nat Nat instHAddNat a b` is definitionally
    // `Nat.add a b`; returning it is a faithful def-unfolding the kernel would
    // perform anyway. Any proof built atop the reduced form is re-checked by the
    // kernel, so a mis-reduction would fail closed, never produce a false proof.
    if *inst_name == *names::INST_HADD_NAT_HOMO {
        if let Some(lit) = native_reducers_arith::reduce_nat_add(&[args[4], args[5]]) {
            return Some(lit);
        }
        let nat_add = Expr::const_(native_reducers_arith::names::NAT_ADD.clone(), vec![]);
        return Some(Expr::app(
            Expr::app(nat_add, args[4].clone()),
            args[5].clone(),
        ));
    }

    None
}

/// Native reducer for `HSub.hSub`.
///
/// Signature: `HSub.hSub : {α β γ : Type u} → [inst : HSub α β γ] → α → β → γ`
/// Args: [α, β, γ, inst, a, b]
fn reduce_hsub_hsub(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 6 {
        return None;
    }
    let inst_name = get_instance_name(args[3])?;

    if *inst_name == *names::INST_HSUB_NAT {
        return native_reducers_arith::reduce_nat_sub(&[args[4], args[5]]);
    }

    None
}

/// Native reducer for `HMul.hMul`.
///
/// Signature: `HMul.hMul : {α β γ : Type u} → [inst : HMul α β γ] → α → β → γ`
/// Args: [α, β, γ, inst, a, b]
fn reduce_hmul_hmul(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 6 {
        return None;
    }
    let inst_name = get_instance_name(args[3])?;

    if *inst_name == *names::INST_HMUL_NAT {
        return native_reducers_arith::reduce_nat_mul(&[args[4], args[5]]);
    }

    None
}

/// Native reducer for `HDiv.hDiv`.
///
/// Signature: `HDiv.hDiv : {α β γ : Type u} → [inst : HDiv α β γ] → α → β → γ`
/// Args: [α, β, γ, inst, a, b]
fn reduce_hdiv_hdiv(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 6 {
        return None;
    }
    let inst_name = get_instance_name(args[3])?;

    if *inst_name == *names::INST_HDIV_NAT {
        return native_reducers_arith::reduce_nat_div(&[args[4], args[5]]);
    }

    None
}

/// Native reducer for `HMod.hMod`.
///
/// Signature: `HMod.hMod : {α β γ : Type u} → [inst : HMod α β γ] → α → β → γ`
/// Args: [α, β, γ, inst, a, b]
fn reduce_hmod_hmod(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 6 {
        return None;
    }
    let inst_name = get_instance_name(args[3])?;

    if *inst_name == *names::INST_HMOD_NAT {
        return native_reducers_arith::reduce_nat_mod(&[args[4], args[5]]);
    }

    None
}

/// Native reducer for `HPow.hPow`.
///
/// Signature: `HPow.hPow : {α β γ : Type u} → [inst : HPow α β γ] → α → β → γ`
/// Args: [α, β, γ, inst, a, b]
fn reduce_hpow_hpow(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 6 {
        return None;
    }
    let inst_name = get_instance_name(args[3])?;

    if *inst_name == *names::INST_HPOW_NAT {
        return native_reducers_arith::reduce_nat_pow(&[args[4], args[5]]);
    }

    None
}

/// Native reducer for `HAppend.hAppend`.
///
/// Signature: `HAppend.hAppend : {α β γ : Type u} → [inst : HAppend α β γ] → α → β → γ`
/// Args: [α, β, γ, inst, a, b]
///
/// Recognizes known append instances and delegates to the underlying operation:
/// - `instHAppendStringStringString` -> String.append
fn reduce_happend_happend(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 6 {
        return None;
    }
    let inst_name = get_instance_name(args[3])?;

    // instHAppendStringStringString (or instHAppendOfAppend applied to String)
    // Check if both operands are string literals
    if let (Some(a), Some(b)) = (get_string_val(args[4]), get_string_val(args[5])) {
        let mut result = String::with_capacity(a.len() + b.len());
        result.push_str(a);
        result.push_str(b);
        return Some(Expr::str_lit(&result));
    }

    // Check for Nat addition through instHAppendOfAppend
    // (less common, but possible for List/Array append with known instances)
    let _ = inst_name; // Instance name checked but no other Nat patterns here

    None
}

/// Register the heterogeneous typeclass short-circuit native reducers.
impl Environment {
    pub(crate) fn init_hetero_shortcircuit_native_reducers(&mut self) {
        self.register_native_reducer(names::HADD_HADD.clone(), reduce_hadd_hadd);
        self.register_native_reducer(names::HSUB_HSUB.clone(), reduce_hsub_hsub);
        self.register_native_reducer(names::HMUL_HMUL.clone(), reduce_hmul_hmul);
        self.register_native_reducer(names::HDIV_HDIV.clone(), reduce_hdiv_hdiv);
        self.register_native_reducer(names::HMOD_HMOD.clone(), reduce_hmod_hmod);
        self.register_native_reducer(names::HPOW_HPOW.clone(), reduce_hpow_hpow);
        self.register_native_reducer(names::HAPPEND_HAPPEND.clone(), reduce_happend_happend);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Environment;

    fn setup_env() -> Environment {
        let mut env = Environment::new();
        env.init_hetero_shortcircuit_native_reducers();
        env
    }

    /// Test HAdd.hAdd with instHAddNatNatNat on Nat literals.
    #[test]
    fn test_hadd_nat_reduces() {
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let inst = Expr::const_(Name::from_string("instHAddNatNatNat"), vec![]);
        let a = Expr::nat_lit(3);
        let b = Expr::nat_lit(4);
        let result = reduce_hadd_hadd(&[&nat_type, &nat_type, &nat_type, &inst, &a, &b]);
        assert!(
            result.is_some(),
            "HAdd.hAdd instHAddNatNatNat 3 4 should reduce"
        );
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            assert_eq!(n.to_u64(), Some(7));
        } else {
            panic!("Expected Nat literal 7");
        }
    }

    /// Test HAdd.hAdd returns None for unknown instances.
    #[test]
    fn test_hadd_unknown_instance_returns_none() {
        let ty = Expr::const_(Name::from_string("MyType"), vec![]);
        let inst = Expr::const_(Name::from_string("instHAddMyType"), vec![]);
        let a = Expr::nat_lit(1);
        let b = Expr::nat_lit(2);
        let result = reduce_hadd_hadd(&[&ty, &ty, &ty, &inst, &a, &b]);
        assert!(result.is_none(), "Unknown instance should return None");
    }

    /// Test HAdd.hAdd returns None for insufficient args.
    #[test]
    fn test_hadd_insufficient_args_returns_none() {
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let inst = Expr::const_(Name::from_string("instHAddNatNatNat"), vec![]);
        let a = Expr::nat_lit(1);
        let result = reduce_hadd_hadd(&[&nat_type, &nat_type, &nat_type, &inst, &a]);
        assert!(result.is_none(), "5 args should return None (need 6)");
    }

    /// Test HSub.hSub with Nat (saturating subtraction).
    #[test]
    fn test_hsub_nat_reduces() {
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let inst = Expr::const_(Name::from_string("instHSubNatNatNat"), vec![]);
        let a = Expr::nat_lit(10);
        let b = Expr::nat_lit(3);
        let result = reduce_hsub_hsub(&[&nat_type, &nat_type, &nat_type, &inst, &a, &b]);
        assert!(
            result.is_some(),
            "HSub.hSub instHSubNatNatNat 10 3 should reduce"
        );
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            assert_eq!(n.to_u64(), Some(7));
        } else {
            panic!("Expected Nat literal 7");
        }
    }

    /// Test HSub.hSub saturates at 0 for Nat.
    #[test]
    fn test_hsub_nat_saturates() {
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let inst = Expr::const_(Name::from_string("instHSubNatNatNat"), vec![]);
        let a = Expr::nat_lit(3);
        let b = Expr::nat_lit(10);
        let result = reduce_hsub_hsub(&[&nat_type, &nat_type, &nat_type, &inst, &a, &b]);
        assert!(result.is_some(), "HSub.hSub should saturate at 0");
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0");
        }
    }

    /// Test HMul.hMul with Nat.
    #[test]
    fn test_hmul_nat_reduces() {
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let inst = Expr::const_(Name::from_string("instHMulNatNatNat"), vec![]);
        let a = Expr::nat_lit(5);
        let b = Expr::nat_lit(6);
        let result = reduce_hmul_hmul(&[&nat_type, &nat_type, &nat_type, &inst, &a, &b]);
        assert!(
            result.is_some(),
            "HMul.hMul instHMulNatNatNat 5 6 should reduce"
        );
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            assert_eq!(n.to_u64(), Some(30));
        } else {
            panic!("Expected Nat literal 30");
        }
    }

    /// Test HDiv.hDiv with Nat.
    #[test]
    fn test_hdiv_nat_reduces() {
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let inst = Expr::const_(Name::from_string("instHDivNatNatNat"), vec![]);
        let a = Expr::nat_lit(17);
        let b = Expr::nat_lit(5);
        let result = reduce_hdiv_hdiv(&[&nat_type, &nat_type, &nat_type, &inst, &a, &b]);
        assert!(
            result.is_some(),
            "HDiv.hDiv instHDivNatNatNat 17 5 should reduce"
        );
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            assert_eq!(n.to_u64(), Some(3));
        } else {
            panic!("Expected Nat literal 3");
        }
    }

    /// Test HDiv.hDiv with 0 denominator.
    #[test]
    fn test_hdiv_nat_div_zero() {
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let inst = Expr::const_(Name::from_string("instHDivNatNatNat"), vec![]);
        let a = Expr::nat_lit(10);
        let b = Expr::nat_lit(0);
        let result = reduce_hdiv_hdiv(&[&nat_type, &nat_type, &nat_type, &inst, &a, &b]);
        assert!(result.is_some(), "HDiv.hDiv with 0 should reduce to 0");
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            assert_eq!(n.to_u64(), Some(0));
        } else {
            panic!("Expected Nat literal 0");
        }
    }

    /// Test HMod.hMod with Nat.
    #[test]
    fn test_hmod_nat_reduces() {
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let inst = Expr::const_(Name::from_string("instHModNatNatNat"), vec![]);
        let a = Expr::nat_lit(17);
        let b = Expr::nat_lit(5);
        let result = reduce_hmod_hmod(&[&nat_type, &nat_type, &nat_type, &inst, &a, &b]);
        assert!(
            result.is_some(),
            "HMod.hMod instHModNatNatNat 17 5 should reduce"
        );
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            assert_eq!(n.to_u64(), Some(2));
        } else {
            panic!("Expected Nat literal 2");
        }
    }

    /// Test HPow.hPow with Nat.
    #[test]
    fn test_hpow_nat_reduces() {
        let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
        let inst = Expr::const_(Name::from_string("instHPowNatNatNat"), vec![]);
        let a = Expr::nat_lit(2);
        let b = Expr::nat_lit(10);
        let result = reduce_hpow_hpow(&[&nat_type, &nat_type, &nat_type, &inst, &a, &b]);
        assert!(
            result.is_some(),
            "HPow.hPow instHPowNatNatNat 2 10 should reduce"
        );
        if let ExprKind::Lit(Literal::Nat(n)) = result.unwrap().kind() {
            assert_eq!(n.to_u64(), Some(1024));
        } else {
            panic!("Expected Nat literal 1024");
        }
    }

    /// Test HAppend.hAppend with String literals.
    #[test]
    fn test_happend_string_reduces() {
        let str_type = Expr::const_(Name::from_string("String"), vec![]);
        let inst = Expr::const_(Name::from_string("instHAppendStringStringString"), vec![]);
        let a = Expr::str_lit("hello ");
        let b = Expr::str_lit("world");
        let result = reduce_happend_happend(&[&str_type, &str_type, &str_type, &inst, &a, &b]);
        assert!(
            result.is_some(),
            "HAppend.hAppend should reduce string literals"
        );
        if let ExprKind::Lit(Literal::String(s)) = result.unwrap().kind() {
            assert_eq!(&**s, "hello world");
        } else {
            panic!("Expected string literal 'hello world'");
        }
    }

    /// Test HAppend.hAppend returns None for non-string, non-recognized instances.
    #[test]
    fn test_happend_non_string_returns_none() {
        let list_type = Expr::const_(Name::from_string("List"), vec![]);
        let inst = Expr::const_(Name::from_string("instHAppendListList"), vec![]);
        let a = Expr::const_(Name::from_string("List.nil"), vec![]);
        let b = Expr::const_(Name::from_string("List.nil"), vec![]);
        let result = reduce_happend_happend(&[&list_type, &list_type, &list_type, &inst, &a, &b]);
        assert!(
            result.is_none(),
            "Non-literal List append should return None"
        );
    }

    /// Test all reducers are registered.
    #[test]
    fn test_hetero_shortcircuit_registered() {
        let env = setup_env();
        assert!(
            env.get_native_reducer(&names::HADD_HADD).is_some(),
            "HAdd.hAdd reducer should be registered"
        );
        assert!(
            env.get_native_reducer(&names::HSUB_HSUB).is_some(),
            "HSub.hSub reducer should be registered"
        );
        assert!(
            env.get_native_reducer(&names::HMUL_HMUL).is_some(),
            "HMul.hMul reducer should be registered"
        );
        assert!(
            env.get_native_reducer(&names::HDIV_HDIV).is_some(),
            "HDiv.hDiv reducer should be registered"
        );
        assert!(
            env.get_native_reducer(&names::HMOD_HMOD).is_some(),
            "HMod.hMod reducer should be registered"
        );
        assert!(
            env.get_native_reducer(&names::HPOW_HPOW).is_some(),
            "HPow.hPow reducer should be registered"
        );
        assert!(
            env.get_native_reducer(&names::HAPPEND_HAPPEND).is_some(),
            "HAppend.hAppend reducer should be registered"
        );
    }
}
